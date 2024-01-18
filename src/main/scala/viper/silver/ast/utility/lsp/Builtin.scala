// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2023 ETH Zurich.

package viper.silver.ast.utility.lsp

abstract class BuiltinFeature(val description: String)
object BuiltinFeature {
  case object Import extends BuiltinFeature(
  """Local Import:
    |```
    |import "path/to/local.vpr"
    |```
    |Standard Import:
    |```
    |import <path/to/provided.vpr>
    |```
    |Imports provide a simple mechanism for splitting a Viper program across several source files using the local import. Further, it also makes it possible to make use of programs provided by Viper using the standard import.
    | - A relative or absolute path to a Viper file may be used (according to the Java/Unix style)
    | - `import` adds the imported program as a preamble to the current one
    | - Transitive imports are supported and resolved via depth-first traversal of the import graph
    | - The depth-first traversal mechanism enforces that each Viper file is imported at most once, including in the cases of multiple (indirect) imports of the same file or of recursive imports.
  """.stripMargin)
  case object Macro extends BuiltinFeature(
  """C-style, syntactically expanded macro.
    |Macros are not type-checked until after expansion. However, macro bodies must be well-formed assertions/statements.
    |Macros may have any number of (untyped) parameter names (e.g. a and b above).
    |There are two kinds of macros:
    | - Macros defining assertions (or expressions or types) include the macro definition whitespace-separated afterwards (e.g. plus above)
    | - Macros defining statements include their definitions within braces (e.g. link above)
  """.stripMargin)
  case object Field extends BuiltinFeature(
  """Every object has all fields (there are no classes in Viper).
    |Reasoning about the heap of a Viper program is governed by field permissions,
    |which specify the heap locations that a statement, an expression or an assertion may access (read and/or modify).
    |Heap locations can be accessed only if the corresponding permission is held by the currently verified method.
    |The simplest form of field permission is the exclusive permission to a heap location x.f;
    |it expresses that the current method may read and write to the location, whereas other methods or threads are not allowed to access it in any way.
  """.stripMargin)
  case object Method extends BuiltinFeature(
  """Methods can be viewed as a means of abstraction over a sequence of operations (i.e. the execution of a potentially-unbounded number of statements).
    |The caller of a method observes its behavior exclusively through the method's signature and its specification (its preconditions and postconditions).
    |Viper method calls are treated modularly: for the caller of a method, the method's implementation can be thought of as invisible.
    |Calling a method may result in modifications to the program state, therefore method calls cannot be used in specifications.
    |On the one hand, the caller of a method must first satisfy the assertions in its precondition in order to obtain the assertions from its postcondition.
    |On the other hand, in order to verify a method itself, Viper must prove that the method's implementation adheres to the method's specification.
  """.stripMargin.replaceAll("\n", " "))
  case object Function extends BuiltinFeature(
  """Functions can be viewed as a means of abstraction over (potentially state-dependent) expressions.
    |Generally, the caller of a function observes three things.
    |First, the precondition of the function is checked in the state in which the function is called.
    |The precondition may include assertions denoting resources, such as permissions to field locations that the the function may read from.
    |Second, the function application's result value is equated with the expression in the function's body (if provided);
    |note that this usage of the function's implementation is a difference from the handling of methods.
    |Third, the function's postconditions are assumed.
    |The postcondition of a function may not contain resource assertions (e.g. denoting field permissions):
    |all resources from the precondition are automatically returned after the function application.
  """.stripMargin.replaceAll("\n", " "))
  case object Predicate extends BuiltinFeature(
  """Predicates can be viewed as a means of abstraction over assertions (including resources such as field permissions).
    |The body of a predicate is an assertion.
    |Unlike functions, predicates are not automatically inlined: to replace a predicate with its body, Viper provides an explicit `unfold` statement.
    |An `unfold` is an operation that changes the program state, replacing the predicate resource with the assertions specified by its body.
    |The dual operation is called a `fold`: folding a predicate replaces the resources specified by its body with an instance of the predicate itself.
  """.stripMargin.replaceAll("\n", " "))
  case object Domain extends BuiltinFeature(
  """Domains enable the definition of additional types, mathematical functions, and axioms that provide their properties.
    |Syntactically, domains consist of a name (for the newly-introduced type), and a block in which a number of function declarations and axioms can be introduced.
  """.stripMargin.replaceAll("\n", " "))
  case object DomainFunction extends BuiltinFeature(
  """The functions declared in a domain are global: one can apply them in any other scope of the Viper program.
    |Domain functions cannot have preconditions; they can be applied in any state.
    |They are also always abstract, i.e., cannot have a defined body.
    |The typical way to attach any meaning to these otherwise-uninterpreted functions, is via domain axioms.
  """.stripMargin.replaceAll("\n", " "))
  case object DomainAxiom extends BuiltinFeature(
  """Domain axioms are global: they define properties of the program which are assumed to hold in all states.
    |Since there is no restriction on the states to which an axiom applies, it must be well-defined in all states;
    |for this reason, domain axioms cannot refer to the values of heap locations, nor to permission amounts (e.g., via perm expressions).
    |In practice, domain axioms are standard (often quantified) first-order logic assertions.
    |Axiom names are used only for readability of the code, but are currently not optional.
  """.stripMargin.replaceAll("\n", " "))

  case object Assert extends BuiltinFeature(
  """The informal semantics of `assert A` is as follows:
    | 1. Assert that all value constraints in `A` hold; if not, verification fails
    | 2. Assert that all permissions denoted (via accessibility predicates) by `A` are currently held; if not, verification fails
  """.stripMargin)
  case object Assume extends BuiltinFeature(
  """The informal semantics of `assume A` is as follows:
    | 1. Assume that all value constraints in `A` hold
  """.stripMargin)
  case object Exhale extends BuiltinFeature(
  """The informal semantics of `exhale A` is as follows:
    | 1. Assert that all value constraints in `A` hold; if not, verification fails
    | 2. Assert that all permissions denoted (via accessibility predicates) by `A` are currently held; if not, verification fails
    | 3. Remove the permissions denoted by `A`
  """.stripMargin)
  case object Inhale extends BuiltinFeature(
  """The informal semantics of `inhale A` is as follows:
    | 1. Add the permissions denoted by `A` to the program state
    | 2. Assume that all value constraints in `A` hold
  """.stripMargin)
  case object LocalVarDecl extends BuiltinFeature(
  """Local variable declarations are used to introduce new variables in the current scope.
    |The type of the variable is specified explicitly, and the variable may optionally be initialized.
    |If a variable is not initialized, its value is defined but unknown.
  """.stripMargin.replaceAll("\n", " "))
  case object Fold extends BuiltinFeature(
  """A fold operation exchanges a predicate body for a predicate instance; roughly speaking, the body is exhaled, and the instance inhaled.
    |However, in contrast to a standard exhale operation,
    |this exhale does not remove information about the locations whose permissions have been exhaled because these permissions are still held,
    |but folded into a predicate.
  """.stripMargin.replaceAll("\n", " "))
  case object Unfold extends BuiltinFeature(
  """An unfold operation exchanges a predicate instance for its body; roughly speaking, the instance is exhaled, and the body inhaled.
    |However, in contrast to a standard exhale operation,
    |this exhale does not remove information about the locations whose permissions have been exhaled because these permissions are still held,
    |but no longer folded into a predicate.
  """.stripMargin.replaceAll("\n", " "))
  case object New extends BuiltinFeature(
  """A `new` statement creates a new object and inhales exclusive permission to all (possibly none) fields listed comma-separated within the parentheses.
    |As a special case, `x := new(*)` inhales permission to all fields declared in the Viper program.
    |Note that neither method calls nor object creation are expressions. Hence, they must not occur as receivers, method arguments, etc.;
    |instead of nesting these constructs, one typically assigns their results first to local variables, and then uses these.
  """.stripMargin.replaceAll("\n", " "))
  case object Package extends BuiltinFeature(
  """There are two ways in which a magic wand instance can be added to the resources held in the program state:
    |they can be inhaled (just as any other Viper resource),
    |or we can instruct Viper to construct a new magic wand instance with a `package` statement.
    |A `package` statement consists of the keyword followed by the desired magic wand instance,
    |along with an optional block of code delimited by braces. The role of a `package` statement is to create (and justify the creation of)
    |a new magic wand instance in the following way:
  """.stripMargin.replaceAll("\n", " ") + """
    | - A subset of the resources held in the current state must be identified as necessary for justifying the new magic wand instance.
    |These must be sufficient resources to ensure that, given the additional resources described in the wand left-hand-side,
    |those on the wand's right-hand-side can be produced. This set of resources is taken from the current state,
    |and is called the footprint of the newly-created magic wand instance.
    | - The `package` operation must check that, given the selected footprint of resources from the current state,
    |in any heap in which the wand's left-hand-side assertion is held, the combination of these resources can be exchanged for the wand right-hand-side.
    |Any field locations framed by permissions in the wand's footprint will be assumed to be unchanged for this check.
    |The check is made during the `package` operation by successively attempting to match the resources required on the right-hand-side with resources provided on the left;
    |if not found on the left-hand-side, the resources must instead be found in the current state (or else the `package` operation fails with a verification error),
    |and are taken for the wand's footprint.
    | - It is often the case that the combination of the wand's left-hand-side and footprint do not directly yield the wand's right-hand-side,
    |but instead can do so after a number of additional operations are performed. These operations can be specified in the block attached to the package statement.
  """.stripMargin)
  case object Apply extends BuiltinFeature(
  """A magic wand instance `A --* B` abstractly represents a resource which, if combined with the resources represented by `A`, can be exchanged for the resources represented by `B`.
    |For example, `A` could represent the permissions to the postfix of a linked-list (where we are now), and `B` could represent the permissions to the entire list;
    |the magic wand then abstractly represents the leftover permissions to the prefix of the list. In this case, both the postfix `A` and a magic wand `A --* B` could be given up,
    |to reobtain `B`, describing the entire list. This “giving up” step, is called applying the magic wand, and is directed in Viper with an `apply` statement.
  """.stripMargin.replaceAll("\n", " "))
  // TODO: quasihavoc
  // TODO: quasihavocall
  // TODO: While
  // TODO: If
  // TODO: Goto
  // TODO: Label
  // TODO: Seq, Set, Multiset, union, intersection, setminus, subset
  // TODO: Map, range, domain
  // TODO: Unfolding, Applying
  // TODO: Old, Let, Forall, Exists, Forperm
  // TODO: acc, wildcard, write, none, epsilon, perm, unique
  // TODO: 
  
  case object TODO extends BuiltinFeature(
  """TODO""".stripMargin.replaceAll("\n", " ")
  )
}

case object DefaultCompletionProposals extends HasCompletionProposals {
  def keywordScope(scope: SuggestionScope): SuggestionBound = SuggestionBound(None, Map(scope -> 0), None)

  // Members
  def member(keyword: String, detail: String, completion: String, doc: String): CompletionProposal =
    CompletionProposal(keyword, CompletionKind.Keyword, None, None, Some(completion), InsertTextFormat.Snippet, Nil, Some(detail), Some(doc), keywordScope(MemberScope))
  def members: Seq[CompletionProposal] = Seq(
    member("method", "Viper Member",
      """method ${1:foo}(${2:arg:Int}) returns (${3:res:Int})
        |  requires ${4:true}
        |  ensures ${5:true}
        |{
        |  ${6:assume true}
        |}""".stripMargin,
      "Methods can be viewed as a means of abstraction over a sequence of operations (i.e. the execution of a potentially-unbounded number of statements). The caller of a method observes its behavior exclusively through the method's signature and its specification (its preconditions and postconditions). Viper method calls are treated modularly: for the caller of a method, the method's implementation can be thought of as invisible. Calling a method may result in modifications to the program state, therefore method calls cannot be used in specifications. On the one hand, the caller of a method must first satisfy the assertions in its precondition in order to obtain the assertions from its postcondition. On the other hand, in order to verify a method itself, Viper must prove that the method's implementation adheres to the method's specification."),
    member("function", "Viper Member",
      """function ${1:foo}(${2:arg:Int}): ${3:Bool}
        |  requires ${4:true}
        |  ensures ${5:true}
        |{
        |  ${6:true}
        |}""".stripMargin,
      "Functions can be viewed as a means of abstraction over (potentially state-dependent) expressions. Generally, the caller of a function observes three things. First, the precondition of the function is checked in the state in which the function is called. The precondition may include assertions denoting resources, such as permissions to field locations that the the function may read from. Second, the function application's result value is equated with the expression in the function's body (if provided); note that this usage of the function's implementation is a difference from the handling of methods. Third, the function's postconditions are assumed. The postcondition of a function may not contain resource assertions (e.g. denoting field permissions): all resources from the precondition are automatically returned after the function application."),
    member("predicate", "Viper Member",
      """predicate ${1:foo}(${2:arg:Ref}) {
        |  ${6:true}
        |}""".stripMargin,
      "Predicates can be viewed as a means of abstraction over assertions (including resources such as field permissions). The body of a predicate is an assertion. Unlike functions, predicates are not automatically inlined: to replace a predicate with its body, Viper provides an explicit `unfold` statement. An `unfold` is an operation that changes the program state, replacing the predicate resource with the assertions specified by its body. The dual operation is called a `fold`: folding a predicate replaces the resources specified by its body with an instance of the predicate itself."),
    member("domain", "Viper Member",
      """domain ${1:MyType[T]} {
        |  ${2}
        |}""".stripMargin,
      "Domains enable the definition of additional types, mathematical functions, and axioms that provide their properties. Syntactically, domains consist of a name (for the newly-introduced type), and a block in which a number of function declarations and axioms can be introduced."),
  )

  // Domain Members
  def domainMember(keyword: String, detail: String, completion: String, doc: String): CompletionProposal =
    CompletionProposal(keyword, CompletionKind.Keyword, None, None, Some(completion), InsertTextFormat.Snippet, Nil, Some(detail), Some(doc), keywordScope(DomainScope))
  def domainMembers: Seq[CompletionProposal] = Seq(
    member("function", "Viper Domain Member",
      """function ${1:foo}(${2:arg:Int}): ${3:Bool}""".stripMargin,
      "The functions declared in a domain are global: one can apply them in any other scope of the Viper program. Domain functions cannot have preconditions; they can be applied in any state. They are also always abstract, i.e., cannot have a defined body. The typical way to attach any meaning to these otherwise-uninterpreted functions, is via domain axioms."),
    member("axiom", "Viper Domain Member",
      """predicate ${1:foo}(${2:arg:Ref}) {
        |  ${6:true}
        |}""".stripMargin,
      "Domain axioms are global: they define properties of the program which are assumed to hold in all states. Since there is no restriction on the states to which an axiom applies, it must be well-defined in all states; for this reason, domain axioms cannot refer to the values of heap locations, nor to permission amounts (e.g., via perm expressions). In practice, domain axioms are standard (often quantified) first-order logic assertions. Axiom names are used only for readability of the code, but are currently not optional."),
  )

  // Statements
  def exprStmt(keyword: String, detail: String, doc: String): CompletionProposal =
    CompletionProposal(keyword, CompletionKind.Keyword, None, None, Some(keyword + " ${1:true}"), InsertTextFormat.Snippet, Nil, Some(detail), Some(doc.stripMargin), keywordScope(StatementScope))
  def statements: Seq[CompletionProposal] = Seq(
    exprStmt("assert", "Viper Statement",
    """The informal semantics of `assert A` is as follows:
      | 1. Assert that all value constraints in `A` hold; if not, verification fails
      | 2. Assert that all permissions denoted (via accessibility predicates) by `A` are currently held; if not, verification fails"""),
    exprStmt("assume", "Viper Statement",
    """The informal semantics of `assume A` is as follows:
      | 1. Assume that all value constraints in `A` hold"""),
    exprStmt("exhale", "Viper Statement",
    """The informal semantics of `exhale A` is as follows:
      | 1. Assert that all value constraints in `A` hold; if not, verification fails
      | 2. Assert that all permissions denoted (via accessibility predicates) by `A` are currently held; if not, verification fails
      | 3. Remove the permissions denoted by `A`"""),
    exprStmt("inhale", "Viper Statement",
    """The informal semantics of `inhale A` is as follows:
      | 1. Add the permissions denoted by `A` to the program state
      | 2. Assume that all value constraints in `A` hold"""),
  )


  override def getCompletionProposals: Seq[CompletionProposal] =
    members ++ domainMembers ++ statements
}
