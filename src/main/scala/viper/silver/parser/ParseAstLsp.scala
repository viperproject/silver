// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2023 ETH Zurich.

package viper.silver.parser

import viper.silver.ast.utility.lsp._
import java.nio.file.Path

// --- Useful common traits ---
trait PLspTokenModifiers {
  def tokenModifiers: Seq[TokenModifier.TokenModifier]
}

trait PLspMaybeSemanticToken extends PNode with PLspTokenModifiers with HasSemanticHighlights {
  def maybeTokenType: Option[TokenType.TokenType]
  def additionalTokenModifiers: Seq[TokenModifier.TokenModifier] = Nil
  override def tokenModifiers: Seq[TokenModifier.TokenModifier] = Nil
  override def getSemanticHighlights: Seq[SemanticHighlight] = (maybeTokenType, RangePosition(this)) match {
    case (Some(tokenType), Some(sp)) => Seq(SemanticHighlight(sp, tokenType, additionalTokenModifiers ++ tokenModifiers))
    case _ => Nil
  }
}
trait PLspSemanticToken extends PLspMaybeSemanticToken {
  def tokenType: TokenType.TokenType
  override def maybeTokenType: Option[TokenType.TokenType] = Some(tokenType)
}

trait PLspDocumentSymbol extends PNode with HasDocumentSymbol {
  override def getSymbolChildren: Seq[DocumentSymbol] = {
    val getSymbol = { case n: HasDocumentSymbol => n.getSymbol }: PartialFunction[PNode, Option[DocumentSymbol]]
    val get = { case Some(s) => s }: PartialFunction[Option[DocumentSymbol], DocumentSymbol]
    subnodes flatMap (_ shallowCollect (getSymbol andThen get))
  }
}

trait PLspHoverHint extends PNode with HasHoverHints {
  def hint: String
  def documentation: Option[String] = None
  def hovers: Seq[PNode]

  override def getHoverHints: Seq[HoverHint] = hovers.flatMap(RangePosition(_)).map(hp => {
    HoverHint(hint, documentation, RangePosition(this), SelectionBoundScope(hp))
  })
}
trait PLspHoverHintRef extends PNode with HasHoverHints {
  def idnuse: PIdnUseLsp

  def hint: Option[String] = idnuse.decl.map(_.hint)
  def documentation: Option[String] = idnuse.decl.flatMap(_.documentation)
  override def getHoverHints: Seq[HoverHint] = (hint, RangePosition(idnuse)) match {
    case (Some(h), Some(ip)) => Seq(HoverHint(h, documentation, RangePosition(this), SelectionBoundScope(ip)))
    case _ => Nil
  }
}

trait PLspStmtWithExp extends PNode with HasSuggestionScopeRanges {
  def e: PExp
  override def getSuggestionScopeRanges: Seq[SuggestionScopeRange] =
    RangePosition(e).map(SuggestionScopeRange(_, ExpressionScope)).toSeq
}

// --- PNode extensions ---
////
// Identifiers (uses and definitions)
////
trait PIdnUseLsp extends PNode with PLspTokenModifiers with HasSemanticHighlights with HasGotoDefinitions with HasReferenceTos {
  def decl: Option[PDeclaration]
  def assignUse: Boolean

  override def tokenModifiers = (if (assignUse) Seq(TokenModifier.Modification) else Nil)

  override def getSemanticHighlights: Seq[SemanticHighlight] = (decl, RangePosition(this)) match {
    case (Some(d), Some(sp)) => Seq(SemanticHighlight(sp, d.tokenType, tokenModifiers ++ d.tokenModifiers))
    case _ => Nil
  }

  override def getGotoDefinitions: Seq[GotoDefinition] = (decl.flatMap(_.declRange), decl.flatMap(_.idndefRange), RangePosition(this)) match {
    case (Some(dp), Some(ip), Some(sp)) => Seq(GotoDefinition(dp, ip, SelectionBoundScope(sp)))
    case _ => Nil
  }

  override def getReferenceTos: Seq[ReferenceTo] = (decl.flatMap(_.idndefRange), RangePosition(this)) match {
    case (Some(ip), Some(tp)) => Seq(ReferenceTo(ip, tp))
    case _ => Nil
  }
}
trait PIdnUseExpLsp extends PIdnUseLsp with PLspHoverHintRef {
  def idnuse = this
}

////
// Keywords
////
trait PReservedLsp[+T <: PReservedString] extends PLspMaybeSemanticToken {
  val rs: T
  override def maybeTokenType = rs.maybeTokenType
  override def tokenModifiers = rs.tokenModifiers
}

trait PReservedStringLsp {
  def maybeTokenType: Option[TokenType.TokenType]
  def tokenModifiers: Seq[TokenModifier.TokenModifier] = Nil
}
trait PKeywordLsp extends PReservedStringLsp {
  override def maybeTokenType = Some(TokenType.Keyword)
}
trait PKeywordStmtLsp extends PKeywordLsp {
  override def tokenModifiers = Seq(TokenModifier.ControlFlow)
}
trait PKeywordTypeLsp extends PReservedStringLsp {
  override def maybeTokenType = Some(TokenType.Type)
}

trait PSymbolLangLsp extends PReservedStringLsp {
  override def maybeTokenType = None
}

trait POperatorLsp extends PReservedStringLsp {
  override def maybeTokenType = Some(TokenType.Operator)
}

////
// Variable declarations
////
trait PAnyVarDeclLsp extends PDeclarationLsp {
  def typ: PType
  override def hint = pretty
  override def detail = Some(typ.pretty)
  override def symbolKind = SymbolKind.Variable
  override def completionScope = Map(ExpressionScope -> 0, StatementScope -> -50)
  override def completionKind = CompletionKind.Variable
}

trait PFormalArgDeclLsp extends PDeclarationLsp {
  override def tokenType = TokenType.Parameter
  override def description = "Argument Binding"
  override def tokenModifiers = Seq(TokenModifier.Readonly)
}
trait PFormalReturnDeclLsp extends PDeclarationLsp {
  override def tokenType = TokenType.Variable
  override def description = "Return Variable"
}
trait PLogicalVarDeclLsp extends PDeclarationLsp  {
  override def tokenType = TokenType.Parameter
  override def description = "Logical Binding"
  override def tokenModifiers = Seq(TokenModifier.Readonly)
}
trait PLocalVarDeclLsp extends PDeclarationLsp {
  override def tokenType = TokenType.Variable
  override def description = "Local Variable"
}
trait PFieldDeclLsp extends PDeclarationLsp {
  def decl: Option[PFields]
  def typ: PType

  override def tokenType = TokenType.Property
  override def symbolKind = SymbolKind.Property
  override def hint = s"${decl.map(_.field.pretty).getOrElse("field")} $pretty"
  override def detail = Some(typ.pretty)
  override def completionScope = Map(ExpressionScope -> 0, StatementScope -> -50)
  override def completionKind = CompletionKind.Property
  override def completionChars = Some(Map('.' -> 50))
  override def description = "Field"
}

////
// Types
////
trait PDomainTypeLsp extends PLspHoverHintRef {
  def domain: PIdnUseLsp
  override def idnuse = domain
}

////
// Operator applications
////
trait POpAppKeywordLsp extends PLspHoverHint with PPrettySubnodes {
  def ops: Seq[PReserved[POperator]]
  def typ: PType
  override def hovers = ops
  
  override def hint: String = {
    val pretty = this.prettyMapped({
      case e: PExp => e.typ.pretty
    })
    s"$pretty: ${typ.pretty}"
  }
}
trait PCallLsp extends PLspHoverHintRef with HasInlayHints {
  def args: Seq[PExp]
  def formalArgs: Seq[PAnyFormalArgDecl] = idnuse.decl match {
    case (Some(function: PGlobalCallable)) => function.formalArgs
    case _ => Nil
  }
  def idnUseMatchesArg(decl: String, use: String): Boolean = {
    val d = decl.toLowerCase()
    val parts = use.toLowerCase().split('_')
    parts.head == d || parts.last == d
  }
  override def getInlayHints: Seq[InlayHint] = formalArgs.zip(args).flatMap {
    case (_: PUnnamedFormalArgDecl, _) => None
    case (PFormalArgDecl(decl, _), PIdnUseExp(use)) if idnUseMatchesArg(decl.name, use) => None
    case (PFormalArgDecl(decl, _), arg) => (RangePosition(decl), RangePosition(arg)) match {
      case (Some(declRp), Some(argRp)) => {
        val declName = InlayHintLabelPart(decl.pretty, None, Some(declRp))
        val label = Seq(declName, InlayHintLabelPart(":"))
        Some(InlayHint(argRp, label, Some(InlayHintKind.Parameter), false, true))
      }
      case _ => None
    }
  }
}






trait PDeclarationLsp extends PNode with PLspHoverHint with PLspSemanticToken with PLspDocumentSymbol with HasCompletionProposals with HasGotoDefinitions with HasReferenceTos {
  def idndef: PIdnDef

  def declRange: Option[RangePosition] = RangePosition(this)
  def idndefRange: Option[RangePosition] = RangePosition(idndef)

  override def additionalTokenModifiers: Seq[TokenModifier.TokenModifier] = Seq(TokenModifier.Definition)

  override def getGotoDefinitions: Seq[GotoDefinition] = (declRange, idndefRange) match {
    case (Some(tp), Some(ip)) => Seq(GotoDefinition(tp, ip, SelectionBoundScope(ip)))
    case _ => Nil
  }
  override def getReferenceTos: Seq[ReferenceTo] = RangePosition(idndef).map(rp => ReferenceTo(rp, rp)).toSeq
  override def hovers: Seq[PNode] = Seq(idndef)

  def completionScope: Map[SuggestionScope, Byte]
  def completionKind: CompletionKind.CompletionKind
  def completionChars: Option[Map[Char, Byte]] = None
  def newText: Option[(String, InsertTextFormat.InsertTextFormat)] = None
  def typeHint: Option[String] = if (this.isInstanceOf[PTypedDeclaration]) this.asInstanceOf[PTypedDeclaration].typ match {
      case typ: PFunctionType => Some(typ.pretty)
      case typ => Some(": " + typ.pretty)
    } else None
  def description: String
  def getCompletionProposals: Seq[CompletionProposal] = RangePosition(this).map(tp => {
      val encScope = if (this.isInstanceOf[PGlobalDeclaration]) None else getEnclosingScope
      val rp = encScope.flatMap(RangePosition(_)).map(sp => RangePosition(tp.file, tp.start, sp._end))
      val bound = SuggestionBound(rp, completionScope, completionChars)
      val format = newText.map(_._2).getOrElse(InsertTextFormat.PlainText)
      CompletionProposal(idndef.pretty, completionKind, typeHint, Some(description), newText.map(_._1), format, Nil, None, None, bound)
    }).toSeq

  def symbolKind: SymbolKind.SymbolKind
  def detail: Option[String] = None
  def isDeprecated: Boolean = false
  def imports: Option[Path] = None
  def tags: Seq[SymbolTag.SymbolTag] = if (isDeprecated) Seq(SymbolTag.Deprecated) else Nil

  override def getSymbol: Option[DocumentSymbol] = (RangePosition(this), RangePosition(idndef)) match {
    case (Some(range), Some(selectionRange)) => Some(DocumentSymbol(idndef.pretty, detail, range, selectionRange, symbolKind, tags, None, getSymbolChildren))
    case _ => None
  }
}

trait PGlobalDeclarationLsp extends PDeclarationLsp with PAnnotated {
  override def documentation: Option[String] = {
    val docs = annotations.filter(_.key.name == "doc").map(_.values.inner.toSeq.map(_.grouped.inner).mkString("\n"))
    if (docs.isEmpty) None else Some(docs.mkString("\n---\n"))
  }
}

trait PAnnotationLsp extends PNode with HasSemanticHighlights {
  def key: PIdnRef
  override def getSemanticHighlights: Seq[SemanticHighlight] = RangePosition(key).map(kp =>
      SemanticHighlight(kp, if (key.name == "doc") TokenType.Comment else TokenType.Decorator)
    ).toSeq
}

trait PStringLiteralLsp extends PNode with HasSemanticHighlights {
  override def getSemanticHighlights: Seq[SemanticHighlight] = RangePosition(this).map(sp => SemanticHighlight(sp, TokenType.String)).toSeq
}

trait PProgramLsp extends PNode with HasSemanticHighlights with HasGotoDefinitions with HasHoverHints with HasFoldingRanges with HasInlayHints with HasCodeLens with HasSignatureHelps with HasReferenceTos with HasCompletionProposals with HasSuggestionScopeRanges {
  override def getSemanticHighlights: Seq[SemanticHighlight] = subnodes.flatMap(_ deepCollect { case sn: HasSemanticHighlights => sn.getSemanticHighlights }).flatten
  override def getGotoDefinitions: Seq[GotoDefinition] = subnodes.flatMap(_ deepCollect { case sn: HasGotoDefinitions => sn.getGotoDefinitions }).flatten
  override def getHoverHints: Seq[HoverHint] = subnodes.flatMap(_ deepCollect { case sn: HasHoverHints => sn.getHoverHints }).flatten
  override def getFoldingRanges: Seq[FoldingRange] = subnodes.flatMap(_ deepCollect { case sn: HasFoldingRanges => sn.getFoldingRanges }).flatten
  override def getInlayHints: Seq[InlayHint] = subnodes.flatMap(_ deepCollect { case sn: HasInlayHints => sn.getInlayHints }).flatten
  override def getCodeLens: Seq[CodeLens] = subnodes.flatMap(_ deepCollect { case sn: HasCodeLens => sn.getCodeLens }).flatten
  override def getSignatureHelps: Seq[SignatureHelp] = subnodes.flatMap(_ deepCollect { case sn: HasSignatureHelps => sn.getSignatureHelps }).flatten
  override def getReferenceTos: Seq[ReferenceTo] = subnodes.flatMap(_ deepCollect { case sn: HasReferenceTos => sn.getReferenceTos }).flatten
  override def getCompletionProposals: Seq[CompletionProposal] =
    DefaultCompletionProposals.getCompletionProposals ++ subnodes.flatMap(_ deepCollect { case sn: HasCompletionProposals => sn.getCompletionProposals }).flatten
  override def getSuggestionScopeRanges: Seq[SuggestionScopeRange] = subnodes.flatMap(_ deepCollect { case sn: HasSuggestionScopeRanges => sn.getSuggestionScopeRanges }).flatten
}
