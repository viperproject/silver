## Release 2023.7

**Date 31/07/23**

### Changes in Viper Language

- Improved language flexibility ([Silver#685](https://github.com/viperproject/silver/pull/685)): The syntax of declarations and assignments is now more permissive, allowing, for example, multiple declarations at once:
  ```
  field n: Ref, m: Ref  // Declare multiple fields at once
  var a: Ref, b: Ref, c: Int  // Declare multiple locals at once
  ```
  Additionally, method calls and new statements can now have fields or newly-declared local variables on their left hand side:
  ```
  var f: Ref := new(n)                   // Declare and initialise locals with `new`
  a, f.n := get_refs()                   // Assign to field from method call
  f.n := new(n)                          // Assign to field with `new`
  ```
  The Viper AST remains unchanged; the newly-supported syntax is desugared into equivalent code that uses the existing Viper AST.
- Annotations ([Silver#666](https://github.com/viperproject/silver/pull/666)): The Viper language now has support for annotations on statements, expressions, and top-level declarations. The syntax for an annotation is ``@key("value", "value2", ...)``, i.e., they have a key which is preceded by an ``@`` sign and a sequence of values written as comma-separated string literals. A single expression/statement/declaration can have multiple annotations. If there are two annotations of the same key, their value sequences are concatenated. In the AST, annotations are represented in the ``info`` field of the annotated AST node using an ``AnnotationInfo`` object.
  Currently, there are two supported annotations: ``@weight("n")`` on quantifiers, where ``n`` is a positive integer, sets the weight of the quantifier in the SMT solver.
  The second annotation is exclusive to the Symbolic Execution backend (see below).
  Unknown annotations are ignored.
- Domain axioms may now refer to non-domain functions that do not have any preconditions ([Silver#698](https://github.com/viperproject/silver/pull/698)).
- Support for chained comparisons ([Silver#713](https://github.com/viperproject/silver/pull/713)): expressions like ``e1 < e2 <= e3 > e4`` can now be parsed and will be desugared to ``(e1 < e2) && (e2 <= e3) && (e3 > e4)``. The AST nodes for comparison operations remain unchanged.
- Two important changes in the termination plugin:
  - The termination plugin now enforces that functions that refer to themselves (or to other functions that call the original function in a mutually-recursive way) in their own postconditions have a ``decreases`` clause ([Silver#711](https://github.com/viperproject/silver/pull/711)). That is, for such functions, one must either prove termination using a ``decreases`` clause, or explicitly state that termination should be assumed by writing ``decreases *``.
    This change addresses frequent issues where users wrote functions that are not well-defined using such postconditions and subsequently reported seemingly unsound behavior (e.g., ([Silver#525](https://github.com/viperproject/silver/issues/525)) and ([Silver#668](https://github.com/viperproject/silver/issues/668))).
  - The termination plugin now automatically imports the default definitions of well-founded orders if ``decreases``-clauses are used but no such definitions are present in the program ([Silver#710](https://github.com/viperproject/silver/pull/710)). That is, it is not longer necessary (but still possible) to write an import statement like ``import <decreases/int.vpr>`` when using a termination measure of type integer.
- The ``Rational`` type, an alias for ``Perm``, is deprecated. Viper issues a warning whenever the type is used.

### Other Viper-level Improvements

- Improved error messages for parse errors ([Silver#702](https://github.com/viperproject/silver/pull/702)) and type errors (([Silver#684](https://github.com/viperproject/silver/pull/684)), ([Silver#724](https://github.com/viperproject/silver/pull/724)))
- Fixed parsing and pretty-printing of scopes ([Silver#704](https://github.com/viperproject/silver/pull/704)), which were previously ommitted under some circumstances by both the pretty-printer and the parser, which could make otherwise valid Viper code invalid. 
- Introduced caching to improve performance of common lookups on the AST (([Silver#659](https://github.com/viperproject/silver/pull/659)) and ([Silver#719](https://github.com/viperproject/silver/pull/719)))
- Viper now reports inferred quantifiers using a ``QuantifierInstantiationsMessage`` ([Silver#653](https://github.com/viperproject/silver/pull/653))
- Introduced various new consistency checks for invalid code that used to crash the backends or lead to unexpected behavior:
  - ``perm``-expressions are no longer allowed in function postconditions ([Silver#681](https://github.com/viperproject/silver/pull/681))
  - ``wildcard`` is no longer allowed as part of compound expressions ([Silver#700](https://github.com/viperproject/silver/pull/700))
  - empty ADTs are rejected ([Silver#696](https://github.com/viperproject/silver/pull/696))
  - predicate argument expressions must be pure ([Silver#721](https://github.com/viperproject/silver/pull/721))
- Labelled ``old``-expressions may now be used as triggers ([Silver#695](https://github.com/viperproject/silver/pull/695))
- Various small fixes for crashes or other incorrect behavior.

### Backend-specific Upgrades/Changes

#### Symbolic Execution Backend (Silicon)

- The previously experimental mode ``--moreCompleteExhale`` is no longer experimental, but is now a supported mode that performs exhales and heap lookups in a way that is usually more complete (but possibly slower). However, Silicon's previous exhale mode remains the default. ([Silicon#682](https://github.com/viperproject/silicon/pull/682))
  - The new flag ``--exhaleMode=n``, where ``n`` is 0, 1, or 2, can now be used to select the exhale mode. 0 is the default, 1 is the previous ``moreCompleteExhale`` mode.
  - The new ``exhaleMode`` 2 uses the default exhale mode 0 throughout the program, until it encounters a verification error. When it does, it retries proving the failing assertion using the (more complete) mode 1. Since mode 0 is usually faster than mode 1, mode 2 often results in the best mix of performance and completeness.
  - Additionally, one can now override the exhale mode selected via command line for individual methods using an annotation ``@exhaleMode("n")`` on the method ([Silicon#724](https://github.com/viperproject/silicon/pull/724))
- Via the option ``--prover=Z3-API``, Silicon can now use Z3 as a library via its Java API (([Silicon#633](https://github.com/viperproject/silicon/pull/633)) and ([Silicon#692](https://github.com/viperproject/silicon/pull/692))). Note that this requires a native version of ``libz3java`` to be present on the path Java uses to look for native libraries (which can be set, e.g., via the environment variable``LD_LIBRARY_PATH`` on Linux or ``DYLD_LIBRARY_PATH`` on MacOS).
  Depending on the OS and the Viper program, this option can lead to a significant speedup.
- Silicon now emits warnings in cases where it cannot use the triggers specified by the user ([Silicon#687](https://github.com/viperproject/silicon/pull/687))
- ``old``-expressions in triggers are now interpreted correctly ([Silicon#710](https://github.com/viperproject/silicon/pull/710)); previously, they were sometimes ignored.
- Changed default options used for Z3; the new options have similar performance and completeness characteristics with the supported Z3 version 4.8.7, but perform better with newer versions (tested in particular with 4.12.1) ([Silicon#694](https://github.com/viperproject/silicon/pull/694))
- Silicon no longer creates a ``tmp`` directory containing ``.smt2`` files that log its prover interactions by default ([Silicon#709](https://github.com/viperproject/silicon/pull/709)). The flag ``--disableTempDirectory`` no longer exists. Instead, one can use the new flag ``--enableTempDirectory`` or the flag ``--proverLogFile``. 
- Improved heuristics for handling of quantified permissions, which improves performance in some cases ([Silicon#704](https://github.com/viperproject/silicon/pull/704))
- Fixed some incorrect (too short) timeouts, which could lead to unstable verification results in some cases ([Silicon#705](https://github.com/viperproject/silicon/pull/705))
- Added a new command line flag ``--reportReasonUnknown``, which instructs Silicon to report the reason the SMT solver names for not being able to prove a property (per error)  ([Silicon#701](https://github.com/viperproject/silicon/pull/701)). This flag can be useful to find out whether an error occurred due to non-linear arithmetic or timeouts.
- Fixed four unsoundnesses:
  - Incorrect handling of ``old``-expressions in postconditions of methods called inside a ``package`` statement ([Silicon#699](https://github.com/viperproject/silicon/pull/699))
  - Incorrect handling of ``fold`` statements for predicates that are used inside a quantified permission in the current method ([Silicon#696](https://github.com/viperproject/silicon/pull/696))
  - Incorrect behavior for quantifiers whose bodies have unreachable branches ([Silicon#690](https://github.com/viperproject/silicon/pull/690))
  - Exhale mode 1 now correctly checks permission amounts in function preconditions ([Silicon#682](https://github.com/viperproject/silicon/pull/682))
- Fixed and generalized the experimental mode ``--conditionalizePermissions``, which avoids branching on conditional permission assertions (e.g., ``b ==> acc(x.f)``) by rewriting them to unconditional assertions with conditional permission amounts (e.g., ``acc(x.f, b ? write : none)`` whenever possible ([Silicon#685](https://github.com/viperproject/silicon/pull/685)). For programs with many branches, this option can improve performance.
- Resource triggers on existentials now work correctly ([Silicon#679](https://github.com/viperproject/silicon/pull/679))
- More complete computation of function footprints ([Silicon#684](https://github.com/viperproject/silicon/pull/684))
- Various smaller bug fixes

#### Verification Condition Generation Backend (Carbon)

- Improved encoding of well-definedness checks for field accesses and permission division ([Carbon#451](https://github.com/viperproject/carbon/pull/451)). As a result, Carbon now emits well-definedness errors in the expected order in some cases where this was previously not the case.
- Improved encoding of definedness checks during exhale ([Carbon#457](https://github.com/viperproject/carbon/pull/457)). This fixed both possible unsoundness and incompleteness issues.
- Using stdin instead of a temporary file to communicate with Boogie ([Carbon#456](https://github.com/viperproject/carbon/pull/456))

## Release 2023.1

**Date 25/01/23**

### Changes in Viper Language

- Quasihavoc: New statements ``quasihavoc`` and ``quasihavocall`` allow explicitly losing information about a resource. E.g., ``quasihavoc c ==> P(x)`` havocs the snapshot of resource ``P(x)`` if ``c`` is true and some permission to ``P(x)`` is held, and does nothing otherwise. Semantically equivalent to (conditionally) exhaling the current permission amount to the given resource and inhaling it again, but implemented more efficiently. For more details, see [this report](https://ethz.ch/content/dam/ethz/special-interest/infk/chair-program-method/pm/documents/Education/Theses/Daniel_Zhang_PW.pdf) ([Silver#611](https://github.com/viperproject/silver/pull/611)). Currently, the Symbolic Execution backend (Silicon) fully supports ``quasihavoc`` and ``quasihavocall``, while the Verification Condition Generation backend (Carbon) only supports ``quasihavoc`` for field and predicate resources and does not suport ``quasihavocall``.
- Syntax for backend types added in the form of domains with interpretations: Domains can be annotated with interpretations for different backends. E.g., 
``domain myBV interpretation (SMTLIB: “(_ BitVec 32)”, Boogie: “bv32”) { ... }``
will be interpreted by Silicon as the SMTLIB type ``(_ BitVec 32)`` and by Carbon as the Boogie type ``bv32``. Similarly, domain functions can be annotated with SMTLIB interpretations. ([Silver#638](https://github.com/viperproject/silver/pull/638))

### Viper API Changes

- **Breaking change**: The plugin API has been extended with a method to transform verification results for individual entities, in addition to the existing method to transform the verification result for the entire Viper program. Plugins should implement *both* methods; the former is used to transform verification results for individual members that are streamed via the Reporter interface ([Silver#641](https://github.com/viperproject/silver/pull/641)). Additionally, the signature of the existing method has been changed in order to remove the need for plugins to maintain state.
- Experimental quantifier weight support: Quantifiers can be given a weight to be used by the SMT solver by annotating them with special WeightedQuantifier info objects  ([Silver#633](https://github.com/viperproject/silver/pull/633)). Currently only available on the AST level (without syntax support), and only supported in the Symbolic Execution backend.
- **Breaking change**: AST nodes for BackendFunctions have been changed to accommodate the new syntax for interpreted domains (see above): Among other small changes, BackendFunc objects no longer exist, and are replaced by DomainFuncs with interpretations. ([Silver#638](https://github.com/viperproject/silver/pull/638))

### Other Viper-level Improvements

- Improved pretty-printing of ASTs ([Silver#616](https://github.com/viperproject/silver/pull/616))
- Improved parsing and better consistency checks for invalid triggers, invalid predicate accesses, and invalid domain types ([Silver#601](https://github.com/viperproject/silver/pull/601)), ([Silver#614](https://github.com/viperproject/silver/pull/614)), ([Silver#626](https://github.com/viperproject/silver/pull/626)), ([Silver#643](https://github.com/viperproject/silver/pull/643))
- Improved type checking performance for large methods ([Silver#631](https://github.com/viperproject/silver/pull/631))
- Termination plugin generates simpler code ([Silver#613](https://github.com/viperproject/silver/pull/613)) and supports more complex expressions ([Silver#618](https://github.com/viperproject/silver/pull/618))
- Several bug fixes ([Silver#607](https://github.com/viperproject/silver/pull/607)), ([Silver#590](https://github.com/viperproject/silver/pull/590)), ([Silver#636](https://github.com/viperproject/silver/pull/636)), ([Silver#635](https://github.com/viperproject/silver/pull/635))

### Backend-specific Upgrades/Changes

#### Symbolic Execution Backend (Silicon)

- Parallel branch verification: Use option ``--parallelizeBranches`` to verify different branches of a method in parallel. Generally speeds up verification but may lead to non-deterministic verification time. ([Silicon#634](https://github.com/viperproject/silicon/pull/634))
- Parallel Silicon instances: Multiple verifier instances can be used in parallel ([Silicon#635](https://github.com/viperproject/silicon/pull/635)), ([Silver#600](https://github.com/viperproject/silver/pull/600))
- Soundness fixes for several long-standing soundness issues. As a result, standard Silicon currently has no known soundness issues outside of magic wands. Fixes include:
  - Function encoding ([Silicon#376](https://github.com/viperproject/silicon/issues/376)), ([Silicon#369](https://github.com/viperproject/silicon/issues/369))
  - Quantified permission encoding for finite domains ([Silicon#342](https://github.com/viperproject/silicon/issues/342)), ([Silicon#636](https://github.com/viperproject/silicon/issues/636))
  - Quantifier encoding ([Silicon#560](https://github.com/viperproject/silicon/issues/560)), ([Silicon#652](https://github.com/viperproject/silicon/issues/652))
- Improved SymbExLogger is now thread safe and reports records via a SymbLogListener interface ([Silicon#622](https://github.com/viperproject/silicon/pull/622)).
- Multiple performance improvements, mostly related to quantified permissions ([Silicon#668](https://github.com/viperproject/silicon/pull/668)), ([Silicon#649](https://github.com/viperproject/silicon/pull/649)), ([Silicon#651](https://github.com/viperproject/silicon/pull/651)), ([Silver#604](https://github.com/viperproject/silver/pull/604)), ([Silver#605](https://github.com/viperproject/silver/pull/605))
- Fixed crashes and other issues ([Silicon#648](https://github.com/viperproject/silicon/issues/648)), ([Silicon#321](https://github.com/viperproject/silicon/issues/321)), ([Silicon#641](https://github.com/viperproject/silicon/issues/641)), ([Silicon#665](https://github.com/viperproject/silicon/issues/665))

#### Verification Condition Generation Backend (Carbon)

- Boogie Version upgraded to 2.15.9 ([Carbon#441](https://github.com/viperproject/carbon/pull/441))
- Inconsistent interpretation of division and modulo fixed ([Carbon#448](https://github.com/viperproject/carbon/pull/448))
- Boogie and Z3 instances are now stopped if Carbon is interrupted ([Carbon#426](https://github.com/viperproject/carbon/pull/426))

## Release 2022.7

**Date 29/07/22**

### Changes in Viper Language

- ADT plugin added. It is enabled by default, and can be disabled with the `--disableAdtPlugin` command-line option. This plugin converts ADT (abstract datatype) declarations of the form `adt (name) { Constructor1(args) ... }` into domain types with constructors, destructors, discriminants, and corresponding axioms. More information can be found in [the tutorial](https://viper.ethz.ch/tutorial/#adt-plugin) ([Silver#574](https://github.com/viperproject/silver/pull/574))
- Added support for a `refute (expression)` statement. This statement behaves like an assertion, except the expression is expected to be provably false. More information can be found in [the tutorial](https://viper.ethz.ch/tutorial/#assertion-checking) ([Silver#583](https://github.com/viperproject/silver/pull/583))
- Division of two `Perm`-typed expressions is now allowed. ([Silver#572](https://github.com/viperproject/silver/pull/572))
- Typed function application syntax (`(foo(...) : T)`) now parses properly. ([Silver#584](https://github.com/viperproject/silver/pull/584))

### Backend-specific upgrades/changes

#### Symbolic Execution Verifier (Silicon)

- Output sent to the backend solver is now SMT-LIB 2.6 conformant. Additionally, there is experimental support for the CVC5 solver using the `--prover cvc5` command-line option. ([Silicon#609](https://github.com/viperproject/silicon/pull/609))
- Improved counterexamples. Counterexamples are now generated for domain types as well, and are included in the output with the `--counterexample mapped` command-line option. ([Silicon#631](https://github.com/viperproject/silicon/pull/631))

#### Verification Condition Generation Verifier (Carbon)

- **Breaking change**: wildcard `acc` expressions in `exhale` statements are no longer reordered. Behaviour is now consistent with Silicon and all permissions in an `exhale` statement are always exhaled left to right. ([Silicon#30](https://github.com/viperproject/silicon/issues/30), [Carbon#411](https://github.com/viperproject/carbon/pull/411))

### Miscellaneous

- "Chopper" API is now available to front ends. This functionality allows a single Viper file to be split into multiple smaller files that can be verified separately. Dependencies between functions, methods, and predicates are correctly determined to minimise the size of the individual Viper files. ([Silver#589](https://github.com/viperproject/silver/pull/589))
- Upgraded projects to use `sbt` version 1.6.2. ([Silicon#627](https://github.com/viperproject/silicon/pull/627), [Silver#592](https://github.com/viperproject/silver/pull/592))
- Viper IDE uses `.vpr` as its default file extension. ([viper-ide#223](https://github.com/viperproject/viper-ide/pull/223))
- Viper IDE now requires at least Java version 11. ([viper-ide#250](https://github.com/viperproject/viper-ide/pull/250))
- Cache improvements. ([Silver#578](https://github.com/viperproject/silver/pull/578))
- Various bug fixes. ([Carbon#423](https://github.com/viperproject/carbon/pull/423), [Carbon#425](https://github.com/viperproject/carbon/pull/425), [viper-ide#248](https://github.com/viperproject/viper-ide/pull/248), [Silver#496](https://github.com/viperproject/silver/issues/496), [Silver#587](https://github.com/viperproject/silver/pull/587), [Silver#590](https://github.com/viperproject/silver/pull/590))

## Release 2022.2

**Date 28/02/22**

### Changes in Viper Language

- **Breaking change**: As mentioned in the release notes for 2021.7, starting with the 2022.2 release, Viper will check injectivity of inhaled quantified permissions by default, instead of assuming it. In the previous release, this feature was enabled with the `--checkInjectivity` flag. It is now enabled by default and can instead by disabled with the `--assumeInjectivityOnInhale` flag. This change makes the injectivity requirement consistent with other well-definedness conditions in Viper (such as ruling out potential division by zero).

### Backend-specific upgrades/changes

#### Symbolic Execution Verifier (Silicon)

- Added new option to report multiple errors per path, potentially allowing verification to continue beyond a failing pure condition (e.g. assert statement). The command-line argument `--numberOfErrorsToReport` (by default 1, 0 indicates all errors are to be reported) controls how many errors will be reported by the verifier before it stops. ([Silicon#575](https://github.com/viperproject/silicon/pull/575))
- Added new option to report branch conditions in errors using the command-line argument `--enableBranchconditionReporting`. When enabled, errors reported on the command line additionally show a list of conditions or their negations that were reached on the path to the error. ([Silicon#575](https://github.com/viperproject/silicon/pull/575))
- Fixed a memory leak ([Silicon#579](https://github.com/viperproject/silicon/issues/579)).
- When Z3 quantifier reporting is enabled (for example, by passing `--z3Args '"smt.qi.profile=true smt.qi.profile_freq=10000"'` to Silicon), its output is now recognised and printed in Silicon's output, to enable a quick check for likely matching loops. ([Silicon#587](https://github.com/viperproject/silicon/pull/587))
- Removed magic-wand-related heuristics described in ECOOP’15 (these were not generally enabled for standard Viper input files). ([Silicon#589](https://github.com/viperproject/silicon/pull/589))
Bug fixes. ([Silicon#582](https://github.com/viperproject/silicon/issues/582), [Silicon#583](https://github.com/viperproject/silicon/pull/583), [Silicon#584](https://github.com/viperproject/silicon/pull/584))

#### Verification Condition Generation Verifier (Carbon)

- Check that predicate bodies are self-framing. ([Carbon#397](https://github.com/viperproject/carbon/pull/397/))
- Bug fixes. ([Carbon#398](https://github.com/viperproject/carbon/pull/398/))

### Miscellaneous

- CI workflows for Viper tools migrated to GitHub actions.
- Silver AST can now represent all SMT-LIB bitvector functions, although these are not yet supported in the language. ([Silver#537](https://github.com/viperproject/silver/pull/537/))
- Impure assumes rewriter fix. ([Silver#553](https://github.com/viperproject/silver/pull/553/))
- Viper IDE cache can be stored to a file. ([ViperServer#44](https://github.com/viperproject/viperserver/pull/44/))
- Position information fix. ([Silver#555](https://github.com/viperproject/silver/pull/555/))

## Release 2021.7
#### Date 27/07/21     [Download](http://www.pm.inf.ethz.ch/research/viper/downloads.html)

### Changes in Viper Language

* **Breaking change**: Inhaling possibly-negative permission amounts now leads to a verification failure, whereas in previous releases it led to an inconsistent state [(Silver, 522)](https://github.com/viperproject/silver/issues/522). For example, `inhale acc(x.f, e)` for some permission expression `e` will now cause a *failure* if `e` is not known to be non-negative, rather than implicitly assuming this property.
* **Planned future breaking change**: Currently, Viper checks the [injectivity of the receiver expression when exhaling quantified permissions](http://viper.ethz.ch/tutorial/?page=1&section=#receiver-expressions-and-injectivity), but not when inhaling quantified permissions (when this property is currently *assumed*). We [plan to change this](https://github.com/viperproject/silver/issues/531) in the January 2022 release, that is Viper will also check injectivity is known when inhaling quantified permissions. Since this is an important breaking change, we have provided access to it in *this* release but only if the `--checkInjectivity` flag is provided. This flag will be removed in the next release, and the corresponding injectivity checks will be enabled by default.

### Backend-specific upgrades/changes

#### Symbolic Execution Verifier (Silicon)
* Added new option for displaying counterexamples using the `--counterexample mapped` command-line argument. This option produces pretty-printed counterexamples with heap chunks resolved to their contained fields.
* Added a [new option](https://github.com/viperproject/silicon/blob/master/src/main/scala/Config.scala#L456) for selecting different [state consolidation modes](https://github.com/viperproject/silicon/blob/master/src/main/scala/Config.scala#L597) affecting how complete, and thus expensive, a state consolidation is [experimental]
* Added scope-based logging of symbolic execution details ([PR #562](https://github.com/viperproject/silicon/pull/562))


#### Verification Condition Generation Verifier (Carbon)

* Fixed labelled old expressions that potentially refer to labels that have not yet been defined [(Carbon, PR 387)](https://github.com/viperproject/carbon/pull/387)
* Added support for loops formed via gotos  [(Carbon, PR 389)](https://github.com/viperproject/carbon/pull/389)
* Minor bug fixes ([382](https://github.com/viperproject/carbon/issues/382), [386](https://github.com/viperproject/carbon/pull/386))

### Miscellaneous

#### Viper-IDE & ViperServer
* Compatibility with latest versions of Silicon and Carbon incl. latest Viper features (e.g. `Map` types and anonymous axioms).
* Mono is no longer a requirement.
* The JAVA installation has to be version 11 or higher and must be 64-bit.
* The IDE now shows non-critical warning messages. 
* Build version of Viper Tools (i.e. the dependencies) can be configured in the VSCode settings:
  * `Stable` / `Nightly`: the latest Viper Tools in the corresponding build configuration will be used. The [Preferences](https://github.com/viperproject/viper-ide/wiki/Settings:-Preferences) specify from which URL the Viper Tools will be downloaded. The Viper Tools are not automatically updated. They only get installed when they are not present yet or when a manual update is triggered (via the command palette). The installation folder has changed for these two build versions: They always get installed to `<VSCode Installation>/User/globalStorage/viper-admin.viper` where `<VSCode Installation>` corresponds to `~/Library/Application Support/Code` (on macOS), `c:\Users\<user>\AppData\Roaming\Code` (on Windows), and `~/.config/Code` (on Linux).
  * `Local`: uses the Viper Tools located at the path specified as `viperSettings.paths.viperToolsPath`.
* Locating the JAVA installation has been improved. A warning appears if it cannot be uniquely identified. A fixed path to a Java installation can be provided in the settings as `viperSettings.javaSettings.javaBinary` ([more details](https://github.com/viperproject/viper-ide/wiki/Settings:-Java-Settings)).
* Sound effects for a successful or failed verification can be enabled by setting `viperSettings.preferences.enableSoundEffects` to true.
* Minor bug fixes ([#23](https://github.com/viperproject/viperserver/issues/23))

  ---



## Release 2021.1
#### Date 15/02/21     [Download](http://www.pm.inf.ethz.ch/research/viper/downloads.html)

### Changes in Viper Language
* Basic support for partial maps. The associated keywords *domain* and *range* are experimental. Please report any observed incompletenesses w.r.t. map reasoning.

### Optimizations
* Optimized parser for large Viper files [(Silver, 477)](https://github.com/viperproject/silver/pull/477).

### Viper Language API changes:
* **Breaking change**: New Scala (2.13.4) and fastparse version.
* **Breaking change**: The constructor of DomainFuncApp now requires that the function's return type is passed as for standard function applications (and not using call-by-name as before) [(Silver, 490)](https://github.com/viperproject/silver/pull/490).
* Due to the deprecation of the Traversable trait, the Node class now extends the Iterable trait instead. The interface is similar, but the implementation of some methods like *find* and *exists* is less efficient because it internally creates a collection with all the elements on which to iterate over ([Silver, 493](https://github.com/viperproject/silver/pull/493) and [Silver, 497](https://github.com/viperproject/silver/pull/497)).
* New backend support for SMTLib types on the AST-level (particularly bitvectors and floats) [(Silver, 428)](https://github.com/viperproject/silver/pull/428).
* Magic wands used inside predicate definitions of function preconditions generate errors (these usages were never fully supported, but a clear error wasn’t shown). We hope to add support for these cases in future.

### Backend-specific upgrades/changes

* [Symbolic Execution Verifier](https://bitbucket.org/viperproject/silicon/)
  * Several minor bugfixes.
  * Two permission-related incompleteness fixed: [(Silicon, 512)](https://github.com/viperproject/silicon/issues/512) and [(Silicon, 508)](https://github.com/viperproject/silicon/issues/508).
  * Command-line option for avoiding creation of a local temp directory [(Silicon, 15)](https://github.com/viperproject/silicon/issues/15).

* [Verification Condition Generation Verifier](https://bitbucket.org/viperproject/carbon/)
  * Boogie upgrade: Boogie is now built with .NET Core and is shipped with all dependencies. As a result, Mono is not required anymore for Boogie on Linux.
  * Minor fixes
    * Boogie AST changed to support unnamed parameters in domain functions [(Carbon, 363)](https://github.com/viperproject/carbon/issues/363).
    * Fix negative fraction check in quantified permissions [(Carbon, 362)](https://github.com/viperproject/carbon/issues/362).

### Miscellaneous
* The Viper IDE (VSCode extension) cannot yet use the new Boogie version, and thus will continue to use the 2020.7 release.
* Viper performs worse with Z3 4.8.9 than with 4.8.6, thus we recommend the use of Z3 4.8.6.

  ---



## Release 2020.7
#### Date 17/07/20     [Download](http://www.pm.inf.ethz.ch/research/viper/downloads.html)
##### Our repositories are now on GitHub: [github.com/viperproject](https://github.com/viperproject)

### Changes in Viper Language
* Axiom names are now optional [(Silver, 193)](https://github.com/viperproject/silver/issues/193).
For example, we now allow domains such as:
	```
    domain MyDomain {
      function foo(): Int

      axiom  { foo() > 2 }
      axiom  upperlimit { foo() < 8 }
    }
	```
* Experimental support for **termination checks** [tutorial section about termination](http://viper.ethz.ch/tutorial/#termination).
  * This extension provides support for specifying termination measures for heap-dependent functions and using them to prove termination.
  * There is also support for proving termination of methods and loops, but those are still experimental and support for these features as well as the semantics of the specifications might change.
  * Details are explained in the Viper tutorial.
* Experimental support for **counter examples**:
  * Added the command line option `--counterexample`. When using either backend with `--counterexamples=variables`, it will return, along with each verification error, a counter example for the values of all local variables (but not the heap or functions) on the Viper level. Alternatively, using the option `--counterexample=native` will return a backend-specific counter example along with each error that contains the entire model exactly as returned by the SMT solver, i.e., including any renaming and encoding the backends may have performed.

### Bug fixes
* 64-bit Z3 is now shipped with the Windows distribution (the 32-bit version which was inadvertently still being shipped can cause memory issues for some examples) [(Silicon, 375)](https://github.com/viperproject/silicon/issues/375)
* Intermittent Failures on Viper Online (web interface) should no longer happen (but for now we only support the default backend) [(Silver, 264)](https://github.com/viperproject/silver/issues/264)
* Reserved words are declared in only one place in the codebase [(Silver, 301)](https://github.com/viperproject/silver/issues/301)
* The phases used to organise programmatically calling verifiers (frontends, in the codebase) have been made more consistent and flexible [(Silver, 270)](https://github.com/viperproject/silver/issues/270)
* Several examples which had long runtimes are now apparently stable (but we would appreciate any feedback to the contrary!). e.g. [(Silver, 457)](https://github.com/viperproject/silver/issues/457)


### Viper Language API changes:
* The `DomainAxiom` AST node no longer exists, it was replaced by:
  * `NamedDomainAxiom`, providing exactly the same features as `DomainAxiom`.
  * `AnonymousDomainAxiom`, which is similar to the node above except for the absence of the `name` parameter.

### Backend-specific upgrades/changes

* [Symbolic Execution Verifier](https://bitbucket.org/viperproject/silicon/)
  * More-complete aliasing properties can be deduced in programs using quantified permissions [(Silicon, 502)](https://github.com/viperproject/silicon/issues/502)
  * Potential crash removed when using quantifiers and unfolding expressions in a function body [(Silicon, 491)](https://github.com/viperproject/silicon/issues/491)

* [Verification Condition Generation Verifier](https://bitbucket.org/viperproject/carbon/)
  * Axioms used for sequence operations should be more complete (especially for cases such as dropping more elements than a sequence has) [(Carbon, 36)](https://github.com/viperproject/carbon/issues/36)
  * Sequence contains function now works in triggers [(Carbon, 349)](https://github.com/viperproject/carbon/issues/349)
  * Carbon should now kill child Boogie and Z3 processes eagerly on stop(); this behaviour may be setup-dependent so please report any outstanding issues [(Carbon, 225)](https://github.com/viperproject/carbon/issues/225)
  * Predicates whose parameters include bound variables (e.g. from outer-quantifiers) now work in function specifications [(Carbon, 271)](https://github.com/viperproject/carbon/issues/271)
  * Work in progress on correct handling of perm-expressions inside unfolding expressions / quantifiers: some issues have been fixed; a summary of the current status is provided [(Carbon, 348)](https://github.com/viperproject/carbon/issues/348)

---

## Release 2020.1
#### Date 31/01/20     [Download](http://www.pm.inf.ethz.ch/research/viper/downloads.html)

### Changes in Viper Language
* Support for variable scopes. For example, now it is possible
to define two variables with the same name in different branches:
    ```
	if (b) {
        var x: Int := 5;
    } else {
        var x: Bool := true;
    }
	```
* Added support for using field lookups and predicates as triggers, e.g.
    ```
	forall r: Ref :: {r.f} r in s ==> r.f > 0

    forall r: Ref :: {P(r)} r in s ==> (unfolding P(r) in r.f > 0)
	```
    Note: this support still has some [issues](https://bitbucket.org/viperproject/carbon/issues/257) in Viper's VCG-based verifier.

* Added support for trigger annotations on existential quantifiers. These are written and behave analogously to those already supported on forall quantifiers, and are relevant in the logically dual cases, typically when *proving* an existentially-quantified assertion [(189)](https://bitbucket.org/viperproject/silver/issues/189).
* Extended support for Viper plugins (designed to make lightweight Viper front-end tools simple to write). In particular, extending the grammar of the parser via plugins is now possible.
* Removed the experimental built-in function termination checking. An experimental
termination plugin is available: https://bitbucket.org/viperproject/termination-plugin/
Feedback is welcome; we plan support for termination checking in the next release.
* Renamed all example files from .sil to .vpr [(287)](https://bitbucket.org/viperproject/silver/issues/287).
* The unary plus operator has been removed [(108)](https://bitbucket.org/viperproject/silver/issues/271).
* Whitespace between unary operations and their operands is no-longer allowed [(272)](https://bitbucket.org/viperproject/silver/issues/272).
* The `fresh` statement was removed [(87)](https://bitbucket.org/viperproject/silver/issues/87).
* Macros can now take field names as parameters [(170)](https://bitbucket.org/viperproject/silver/issues/170).
* LHS of field assignment statements can now be a macro invocation [(214)](https://bitbucket.org/viperproject/silver/issues/214).
* Warnings are now generated for unused macro parameters [(267)](https://bitbucket.org/viperproject/silver/issues/267).
* Macro definitions are disallowed inside magic wand proof scripts [(215)](https://bitbucket.org/viperproject/silver/issues/215).

### Bug fixes
* Conditional assertions as part of quantified permissions are properly supported, e.g. 
  `inhale forall j : Int :: (j == k ? acc(s.f) : true)` [(260)](https://bitbucket.org/viperproject/silver/issues/260).
* Expression macros with missing bodies no-longer cause spurious parser errors (for next construct) [(273)](https://bitbucket.org/viperproject/silver/issues/273).
* `new(..)` parameterised by identifiers which are present in the program but are not field names now produces an appropriate error message [(247)](https://bitbucket.org/viperproject/silver/issues/247).
* Type checker no longer crashes on ASTs with sharing [(191)](https://bitbucket.org/viperproject/silver/issues/191).
* Macro names are now checked for clashes [(167)](https://bitbucket.org/viperproject/silver/issues/167).
* The AST utility method `Expressions.instantiateVariables` is now capture-avoiding (an additional parameter can be provided to exclude certain names from being chosen when renaming bound variables) [(286)](https://bitbucket.org/viperproject/silver/issues/286).
* Eliminated spurious type error involving #E type when using empty Multisets via macros [(282)](https://bitbucket.org/viperproject/silver/issues/282).
* AST transformation framework's Rewritable is no-longer limited w.r.t. collections of Rewritables [(225)](https://bitbucket.org/viperproject/silver/issues/225).

### Viper Language API changes: 
* `LocalVar` AST node no longer has type as an optional field [(281)](https://bitbucket.org/viperproject/silver/issues/281).
* `Result` AST node no longer has type in its second parameter list [(283)](https://bitbucket.org/viperproject/silver/issues/283).
* `Call` trait, `FuncApp` and `DomainFuncApp` AST nodes no longer have a `formalArgs` field; this information can be obtained from the enclosing `Program` [(241)](https://bitbucket.org/viperproject/silver/issues/241).
* Upgraded all dependencies, libraries, plugins and development environment:
    * SBT 1.2.6, rewriting all build files.
	* Scala 2.12.7
	* fastparse	1.0.0
	* ScalaTest 3.0.5.
	* scallop 3.1.3.
	* jgrapht-core 1.2.0.
	* scala-parser-combinators 1.1.1.
	* commons-io 2.6.
	* guava 26.0.
	* slf4j-api 1.7.25.
	* logback-classic 1.2.3.
	* scala-logging 3.9.0
	* sbt-assembly 0.14.7
	* sbteclipse-plugin	5.2.4.
  

### Backend-specific upgrades/changes
* [Symbolic Execution Verifier](https://bitbucket.org/viperproject/silicon/)
    * Implemented an experimental feature that allows using the quantified
permissions based handling of permissions for all permissions. This
handling of permissions is expected to be more complete and may be faster;
however, the implementation is still in beta state. The feature can be
enabled with the ``--enableMoreCompleteExhale`` flag.
    * (API) Uses logback library instead of log4j for logging.
    * (API) Changed how the verifier reports errors: introduced a reporter class
that is responsible for reporting errors to the user (before errors were
reported via logging). Verification results of a particular method are
reported via the reporter as soon as they become available without
waiting for all methods to be verified.
* [Verification Condition Generation Verifier](https://bitbucket.org/viperproject/carbon/)
    * Quantified permissions with multiple forall-bound variables are now supported [(205)](https://bitbucket.org/viperproject/carbon/issues/205/).
    * Experimental adjustments to the background axioms used for set, sequence and multiset support. These should   mostly add completeness; fewer scenarios should require user assertions to verify. Please report any bugs observed (particularly examples which exhibit poorer performance). In the next release, this will be stabilised, and migrated analogously to Viper's Symbolic Execution back-end. 
    * Old expressions in triggers are now translated correctly [(236)](https://bitbucket.org/viperproject/carbon/issues/236/).
    * Substitution of actuals for formals in method specifications, predicate unfoldings and function preconditions is now capture-avoiding [(262)](https://bitbucket.org/viperproject/carbon/issues/262), [(282)](https://bitbucket.org/viperproject/carbon/issues/282).
    * Quantified predicates without arguments no-longer cause a crash [(279)](https://bitbucket.org/viperproject/carbon/issues/279).

### Other Notes
   * We observed that 'Out of memory' errors can occur for some larger examples if using a 32-bit (rather than 64-bit) version of Z3 [(286)](https://bitbucket.org/viperproject/carbon/issues/286). We recommend always using a 64-bit version.
