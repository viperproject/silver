// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2023 ETH Zurich.

package viper.silver.parser

import viper.silver.ast.utility.lsp._
import java.nio.file.Path
import viper.silver.ast.LineColumnPosition

// --- Useful common traits ---
trait PLspTokenModifiers {
  def tokenModifiers: Seq[TokenModifier.TokenModifier]
}

trait PLspMaybeSemanticToken extends PNode with PLspTokenModifiers with HasSemanticHighlights {
  def maybeTokenType: Option[TokenType.TokenType]
  def tokenPosition: Option[RangePosition] = RangePosition(this)
  def additionalTokenModifiers: Seq[TokenModifier.TokenModifier] = Nil
  override def tokenModifiers: Seq[TokenModifier.TokenModifier] = Nil
  override def getSemanticHighlights: Seq[SemanticHighlight] = (tokenPosition, maybeTokenType) match {
    case (Some(sp), Some(tokenType)) => Seq(SemanticHighlight(sp, tokenType, additionalTokenModifiers ++ tokenModifiers))
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

  def getHoverHintsRaw: Seq[HoverHint] = hovers.flatMap(RangePosition(_)).map(hp => {
    HoverHint(hint, documentation, RangePosition(this), SelectionBoundScope(hp))
  })
  override def getHoverHints = getHoverHintsRaw
}
trait PLspHoverHintRef extends PNode with HasHoverHints {
  def idnref: PLspIdnUse

  def hintRef: Option[String] = idnref.decl.map(_.hint)
  def documentationRef: Option[String] = idnref.decl.flatMap(_.documentation)
  def getHoverHintsRef: Seq[HoverHint] = (hintRef, RangePosition(idnref)) match {
    case (Some(h), Some(ip)) => Seq(HoverHint(h, documentationRef, RangePosition(this), SelectionBoundScope(ip)))
    case _ => Nil
  }
  override def getHoverHints = getHoverHintsRef
}
trait PLspHoverHintBoth extends PLspHoverHint with PLspHoverHintRef {
  override def getHoverHints = getHoverHintsRef ++ getHoverHintsRaw
}

// --- PNode extensions ---
////
// Identifiers (uses and definitions)
////
trait PLspIdnUse extends PNode with PLspTokenModifiers with HasSemanticHighlights with HasGotoDefinitions with HasReferenceTos {
  def decl: Option[PDeclarationInner]
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
trait PLspIdnUseExp extends PLspIdnUse with PLspExpRef {
  override def idnref = this
}

////
// Keywords
////
trait PLspReserved[+T <: PReservedString] extends PLspMaybeSemanticToken with HasHoverHints {
  val rs: T
  override def maybeTokenType = rs.maybeTokenType
  override def tokenModifiers = rs.tokenModifiers

  // Only display hover if there is documentation
  override def getHoverHints: Seq[HoverHint] = (rs.documentationAsHint, RangePosition(this)) match {
    case (true, Some(rp)) => Seq(HoverHint(this.pretty, rs.documentation.map(_.description), Some(rp), SelectionBoundScope(rp)))
    case _ => Nil
  }
}

trait PLspReservedString {
  def maybeTokenType: Option[TokenType.TokenType]
  def tokenModifiers: Seq[TokenModifier.TokenModifier] = Nil
}
trait PLspKeyword extends PLspReservedString {
  override def maybeTokenType = Some(TokenType.Keyword)
}
trait PLspKeywordStmt extends PLspKeyword {
  override def tokenModifiers = Seq(TokenModifier.ControlFlow)
}
trait PLspKeywordType extends PLspReservedString {
  override def maybeTokenType = Some(TokenType.Type)
}

trait PLspSymbolLang extends PLspReservedString {
  override def maybeTokenType = None
}

trait PLspOperator extends PLspReservedString {
  override def maybeTokenType = Some(TokenType.Operator)
}

////
// Variable declarations
////
trait PLspAnyVarDecl extends PLspDeclaration {
  def typeMaybe: Option[PType]
  override def hint = pretty
  override def detail = typeMaybe.map(_.pretty)
  override def symbolKind = SymbolKind.Variable
  override def completionScope = Map(ExpressionScope -> 0, StatementScope -> -50)
  override def completionKind = CompletionKind.Variable
}
trait PLspTypedVarDecl extends PLspAnyVarDecl {
  def typ: PType
  override def typeMaybe = Some(typ)
}

trait PLspFormalArgDecl extends PLspDeclaration with PLspTypedVarDecl {
  override def tokenType = TokenType.Parameter
  override def description = "Argument Binding"
  override def tokenModifiers = Seq(TokenModifier.Readonly)
}
trait PLspFormalReturnDecl extends PLspDeclaration with PLspTypedVarDecl {
  override def tokenType = TokenType.Variable
  override def description = "Return Variable"
}
trait PLspLogicalVarDecl extends PLspDeclaration with PLspTypedVarDecl {
  override def tokenType = TokenType.Parameter
  override def description = "Logical Binding"
  override def tokenModifiers = Seq(TokenModifier.Readonly)
}
trait PLspLocalVarDecl extends PLspDeclaration with PLspTypedVarDecl {
  override def tokenType = TokenType.Variable
  override def description = "Local Variable"
}
trait PLspFieldDecl extends PLspDeclaration {
  def decl: Option[PFields]
  def typ: PType

  override def tokenType = TokenType.Property
  override def symbolKind = SymbolKind.Property
  override def hint = s"${decl.map(_.field).getOrElse(PReserved.implied(PKw.Field)).pretty}$pretty"
  override def detail = Some(typ.pretty)
  override def completionScope = Map(ExpressionScope -> 0, StatementScope -> -50)
  override def completionKind = CompletionKind.Property
  override def completionChars = Some(Map('.' -> 50))
  override def description = "Field"
}

////
// Types
////
trait PLspDomainType extends PLspHoverHintRef {
  def domain: PLspIdnUse
  override def idnref = domain
}

////
// Operator applications
////

// Operators which don't have a `PIdnRef`
trait PLspExp extends PLspHoverHint with PPrettySubnodes {
  def ops: Seq[PReserved[POperator]] = subnodes flatMap (_ shallowCollect({
    case r: PReserved[_] if r.rs.isInstanceOf[POperator] => Some(r.asInstanceOf[PReserved[POperator]])
    case _: PExp => None
  }) flatMap (r => r))
  def typ: PType
  override def hovers = ops

  override def hint: String = {
    val pretty = this.prettyMapped({
      case e: PExp => e.typ.pretty
    })
    s"$pretty: ${typ.pretty}"
  }
  override def documentation: Option[String] = ops.flatMap(_.rs.documentation).headOption.map(_.description)
}
trait PLspExpRef extends PLspExp with PLspHoverHintBoth

trait PLspCall extends PLspExpRef with HasInlayHints {
  def args: Seq[PExp]
  def formalArgs: Seq[PAnyFormalArgDecl] = idnref.decl match {
    case (Some(function: PGlobalCallable)) => function.formalArgs
    case _ => Nil
  }
  def idnUseMatchesArg(decl: String, use: String): Boolean = {
    val d = decl.toLowerCase()
    val parts = use.toLowerCase().split('_')
    parts.head == d || parts.last == d
  }
  override def getInlayHints: Seq[InlayHint] = formalArgs.zip(args).flatMap {
    case (PDomainFunctionArg(None, _, _), _) => None
    case (PDomainFunctionArg(Some(decl), _, _), PIdnUseExp(use)) if idnUseMatchesArg(decl.name, use) => None
    case (PFormalArgDecl(decl, _, _), PIdnUseExp(use)) if idnUseMatchesArg(decl.name, use) => None
    case (PFormalArgDecl(decl, _, _), arg) => (RangePosition(decl), RangePosition(arg)) match {
      case (Some(declRp), Some(argRp)) => {
        val declName = InlayHintLabelPart(decl.pretty, None, Some(declRp))
        val label = Seq(declName, InlayHintLabelPart(":"))
        Some(InlayHint(argRp, label, Some(InlayHintKind.Parameter), false, true))
      }
      case _ => None
    }
  }
}

////
// Statements
////

trait PLspStmtWithExp extends PNode with HasSuggestionScopeRanges {
  def e: PExp
  override def getSuggestionScopeRanges: Seq[SuggestionScopeRange] =
    RangePosition(e).map(SuggestionScopeRange(_, ExpressionScope)).toSeq
}

////
// Members
////

trait PLspCallable extends PLspDeclaration with HasSuggestionScopeRanges with HasFoldingRanges with HasSignatureHelps {
  def keyword: PReserved[_]
  def args: PDelimited.Comma[PSym.Paren, PAnyFormalArgDecl]
  def formalArgs: Seq[PAnyFormalArgDecl]
  def bodyRange: Option[RangePosition]
  def returnString: Option[String]
  def pres: PDelimited[PSpecification[PKw.PreSpec], Option[PSym.Semi]]
  def posts: PDelimited[PSpecification[PKw.PostSpec], Option[PSym.Semi]]

  override def hint: String = {
    val firstLine = s"${keyword.pretty}${idndef.pretty}${args.pretty}${returnString.getOrElse("")}"
    val contract = (pres.toSeq ++ posts.toSeq).map(_.pretty)
    val bodyString = bodyRange.map(_ => if (contract.length > 0) "\n{ ... }" else " { ... }").getOrElse("")
    s"$firstLine${contract.mkString}$bodyString"
  }
  override def getSignatureHelps: Seq[SignatureHelp] = {
    val bound = SelectionBoundKeyword(idndef.name)
    val start = SignatureHelpPart(false, s"${keyword.pretty} ${idndef.pretty}(", None)
    val args = formalArgs.map(fa => SignatureHelpPart(true, fa.pretty, None))
    val tail = SignatureHelpPart(false, ")" + returnString.getOrElse(""), None)
    def addCommas(args: Seq[SignatureHelpPart]): Seq[SignatureHelpPart] = if (args.length <= 1) args :+ tail else {
      args.head +: SignatureHelpPart(false, ", ", None) +: addCommas(args.drop(1))
    }
    val help = start +: addCommas(args)
    Seq(SignatureHelp(help, documentation, bound))
  }
  override def getFoldingRanges: Seq[FoldingRange] = {
    val thisRange = RangePosition(this).filter(rp => rp.start.line != rp._end.line)
    val bodyRangeFilter = bodyRange.filter(rp => rp.start.line != rp._end.line)
    val sameStart = thisRange.zip(bodyRangeFilter).map(rps => rps._1.start.line == rps._2.start.line).getOrElse(false)
    val ranges = if (sameStart) thisRange.toSeq else (thisRange.toSeq ++ bodyRangeFilter.toSeq)
    ranges.map(FoldingRange(_))
  }
  override def newText: Option[(String, InsertTextFormat.InsertTextFormat)] = {
    val args = formalArgs.zipWithIndex.map {
      case (ad: PFormalArgDecl, i) => s"$${${i+1}:${ad.idndef.pretty}}"
      case (_, i) => s"$${${i+1}:arg${i+1}}"
    }
    Some((s"${idndef.pretty}(${args.mkString(", ")})", InsertTextFormat.Snippet))
  }
}

trait PLspAnyFunction extends PLspCallable {
  override def tokenType = TokenType.Function
  override def symbolKind = SymbolKind.Function
  override def returnString: Option[String] = Some(s"${c.pretty}${resultType.pretty}")
  // override def getGotoDefinitions: Seq[GotoDefinition] = super.getGotoDefinitions ++ formalArgs.map(_.getGotoDefinitions)

  def c: PSym.Colon
  def resultType: PType

  override def getSuggestionScopeRanges: Seq[SuggestionScopeRange] =
    RangePosition(this).map(SuggestionScopeRange(_, CallableSignatureScope)).toSeq ++
    bodyRange.map(SuggestionScopeRange(_, ExpressionScope)).toSeq
  override def completionScope: Map[SuggestionScope,Byte] = Map(ExpressionScope -> 0, StatementScope -> -50)
  override def completionKind: CompletionKind.CompletionKind = CompletionKind.Function
}



trait PLspDeclaration extends PNode with PLspHoverHint with PLspSemanticToken with PLspDocumentSymbol with HasCompletionProposals with HasGotoDefinitions with HasReferenceTos {
  def idndef: PIdnDef

  def declRange: Option[RangePosition] = RangePosition(this)
  def idndefRange: Option[RangePosition] = RangePosition(idndef)
  override def tokenPosition: Option[RangePosition] = idndefRange

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

trait PLspGlobalDeclaration extends PLspDeclaration with PAnnotated {
  override def documentation: Option[String] = {
    val docs = annotations.filter(_.key.str == "doc").map(_.values.inner.toSeq.map(_.grouped.inner).mkString("\n"))
    if (docs.isEmpty) None else Some(docs.mkString("\n\n"))
  }
}

trait PLspAnnotation extends PNode with HasSemanticHighlights {
  def key: PRawString
  def values: PGrouped[PSym.Paren, PDelimited[PStringLiteral, PSym.Comma]]
  // Make strings display as comments if the annotation is a doc annotation
  val initValues = if (key.str == "doc") values.inner.toSeq foreach (_.tokenType = TokenType.Comment)

  // Gets the range positions of all lines of the annotation
  def multilineRangePositions: Seq[RangePosition] = (RangePosition(this), RangePosition(values.l), RangePosition(values.r)) match {
    case (Some(rp), Some(lRp), Some(rRp)) => {
      var old = Option(RangePosition(rp.file, rp.start, lRp._end))
      def join(old: RangePosition, added: RangePosition): Seq[RangePosition] =
        if (old._end.line == added.start.line) Seq(RangePosition(rp.file, old.start, added._end))
        else Seq(old, added)
      values.inner.toSeq.zip(values.inner.delimiters.map(Some(_)) :+ None).flatMap { case (s, c) => {
        val res = s.multilineRangePositions.flatMap(sRp => {
          val res = old.map(join(_, sRp)).getOrElse(Seq(sRp))
          old = None
          res
        })
        val last = c.flatMap(RangePosition(_)).map(join(res.last, _)).getOrElse(Seq(res.last))
        old = Some(last.last)
        if (last.length == 1) res.dropRight(1) else res
      }} ++ join(old.get, rRp)
    }
    case _ => Nil
  }
  override def getSemanticHighlights: Seq[SemanticHighlight] = RangePosition(key).map(SemanticHighlight(_, TokenType.Decorator)).toSeq
}

trait PLspStringLiteral extends PNode with HasSemanticHighlights {
  def grouped: PGrouped[_, String]
  // Semantic highlights which span multiple lines are not supported, thus we must break the string up
  // Use the line lengths of the string literal that we have saved to calculate the range position for each line
  def multilineRangePositions: Seq[RangePosition] = RangePosition(this).toSeq.flatMap(rp => {
      var last = rp.start
      val lines = grouped.inner.split("\n")
      val startLen = grouped.l.rs.symbol.length()
      val endLen = grouped.r.rs.symbol.length()
      val linesRp = lines.zipWithIndex.map(line => {
        val delta = line._1.length()
        val end = (line._2 == 0, line._2 == lines.length - 1) match {
          case (true, true) => last.deltaColumn(delta + startLen + endLen)
          case (true, false) => last.deltaColumn(delta + startLen)
          case (false, true) => last.deltaColumn(delta + endLen)
          case (false, false) => last.deltaColumn(delta)
        }
        val lineRp = RangePosition(rp.file, last, end)
        last = LineColumnPosition(last.line + 1, 1)
        lineRp
      })
      assert(linesRp.last._end.line == rp._end.line, s"Multiline string literal range end line positions do not match up: ${linesRp.last} vs $rp")
      assert(linesRp.last._end.column == rp._end.column, s"Multiline string literal range end column positions do not match up: ${linesRp.last} vs $rp")
      linesRp
    })
  var tokenType: TokenType.TokenType = TokenType.String
  override def getSemanticHighlights: Seq[SemanticHighlight] = multilineRangePositions.map(sp => SemanticHighlight(sp, tokenType)).toSeq
}

trait PLspProgram extends PNode with HasSemanticHighlights with PLspDocumentSymbol with HasGotoDefinitions with HasHoverHints with HasFoldingRanges with HasInlayHints with HasCodeLens with HasSignatureHelps with HasReferenceTos with HasCompletionProposals with HasSuggestionScopeRanges {
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
  override def getSymbol: Option[DocumentSymbol] = None
}
