## Release 2020.7
#### Date 17/07/20     [Download](http://www.pm.inf.ethz.ch/research/viper/downloads.html)

### Changes in Viper Language
* Axiom names are now optional.
* Experimental support for **termination checks** via dedicated plugin [Link to section in the tutorial](). **TBD**
* Experimental support for **counter examples**:
  * Added the command line option `--counterexample` to return, for each verification error, either a backend-independent counter example for only the values of local variables, or a native backend-specific counter example (in both Silicon and Carbon).

### Bug fixes
* Z3 "out of memory"s on example quantifiedpredicates/basic/partial_permissions.sil [(Silicon, 375)](https://github.com/viperproject/silicon/issues/375)
* Potential matching loop in all/sequences/sequences.vpr [(Silicon, 406)](https://github.com/viperproject/silicon/issues/406)
* Add well-definedness checks for built-in axiomatisations [(Carbon, 36)](https://github.com/viperproject/carbon/issues/36)
* The consistency check and fast parse have duplicated code which is differing, factoring is needed [(Silver, 301)](https://github.com/viperproject/silver/issues/301)
* QP example third_party/fmse-2015-04-16.sil takes too long to verify [(Silicon, 289)](https://github.com/viperproject/silicon/issues/289)
* Check type-soundness of Expressions.instantiateVariables and Expressions.renameVariables [(Silver, 112)](https://github.com/viperproject/silver/issues/112)
* Refactor LHS old label and remove FastParse references [(Silver, 441)](https://github.com/viperproject/silver/issues/441)
* Test case linked-list-predicates doesn't reliably terminate [(Silver, 234)](https://github.com/viperproject/silver/issues/234)
* Make axiom names optional [(Silver, 193)](https://github.com/viperproject/silver/issues/193)
* Z3 4.8.6 nightly exhausts memory on issues/carbon/0210.sil — matching loop? [(Silicon, 397)](https://github.com/viperproject/silicon/issues/397)
* Examples repo: cav2017/FollyRWSpinlock_err_mod.sil doesn't parse [(Silver, 446)](https://github.com/viperproject/silver/issues/446)
* Intermittent Internal Failures on Viper Online [(Silver, 264)](https://github.com/viperproject/silver/issues/264)
* Error parsing programs in examples [(Silver, 457)](https://github.com/viperproject/silver/issues/457)
* Test case quantifiedpredicates/issues//block_array.sil is sporadically timing-out (on the build server) [(Carbon, 176)](https://github.com/viperproject/carbon/issues/176)
* Refactoring of the frontend phases [(Silver, 270)](https://github.com/viperproject/silver/issues/270)
* Non-aliasing incompleteness when using QPs [(Silicon, 502)](https://github.com/viperproject/silicon/issues/502)
* Failing assert after magic wand application [(Silicon, 498)](https://github.com/viperproject/silicon/issues/498)
* Verification aborted exceptionally: pure quantifier and unfolding expression in function body [(Silicon, 491)](https://github.com/viperproject/silicon/issues/491)
* Failing assert after magic wand application [(Carbon, 358)](https://github.com/viperproject/carbon/issues/358)
* Cannot restore full permission after a loop encoded with labels [(Carbon, 352)](https://github.com/viperproject/carbon/issues/352)
* Sequence containment does not work in triggers [(Carbon, 349)](https://github.com/viperproject/carbon/issues/349)

### Viper Language API changes:

### Backend-specific upgrades/changes

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
