# Test Suite for Magic Wand Snap Functions

This folder contains Viper test files that I used when working on MagicWandSnapFunctions for the Silicon project.

## Overview

| Name                                                                       | Description                                                                                     | Expected Result |
|----------------------------------------------------------------------------|-------------------------------------------------------------------------------------------------|-----------------|
| [basic-bool.vpr](./basic-bool.vpr)                                         | Boolean Magic Wand with trivial LHS                                                             | ✓               |
| [basic-int.vpr](./basic-int.vpr)                                           | Integer Magic Wand with trivial LHS                                                             | ✓               |
| [basic-lhs-eq-rhs.vpr](./basic-lhs-eq-rhs.vpr)                             | Integer Magic Wand with LHS = RHS                                                               | ✓               |
| [basic-lhs-lt-rhs.vpr](./basic-lhs-lt-rhs.vpr)                             | Integer Magic Wand with LHS < RHS                                                               | ✓               |
| [basic-lhs-gt-rhs.vpr](./basic-lhs-gt-rhs.vpr)                             | Integer Magic Wand with LHS > RHS                                                               | ✓               |
| [applying-twice-bool.vpr](./applying-twice-bool.vpr)                       | Applying the magic wand multiple times. Original version leaks information into the outer state | ×               |
| [assign-applying-bool.vpr](./assign-applying-bool.vpr)                     | Assigning result of applying expression to the same field using booleans                        | ×               |
| [assign-applying-int.vpr](./assign-applying-int.vpr)                       | Assigning result of applying expression to the same field using integers                        | ×               |
| [inhaling-magic-wand.vpr](./inhaling-magic-wand.vpr)                       | Inhaling a magic wand                                                                           | ✓               |
| [predicates-in-magic-wands.vpr](./predicates-in-magic-wands.vpr)           | Magic wand with predicates                                                                      | ✓               |
| [example-list.vpr](./example-list.vpr)                                     | Iterate over a List                                                                             | ✓               |
| [applying-twice-quantified-wand.vpr](./applying-twice-quantified-wand.vpr) | Applying a quantified magic wand multiple times.                                                | ✓               |
| [applying-twice-quantified-lhs.vpr](./applying-twice-quantified-lhs.vpr)   | Applying a magic wand multiple times with a quantified expression on the LHS.                   | ✓               |
| [applying-twice-qp-fields.vpr](./applying-twice-qp-fields.vpr)             | Test from QPFields.vpr adapted to test some unsound behavior.                                   | ✓               |
| [applying-twice-qp-predicates.vpr](./applying-twice-qp-predicates.vpr)     | Test from QPPredicates.vpr adapted to test some unsound behavior.                               | ✓               |
| [quantified-magic-wands.vpr](./quantified-magic-wands.vpr)                 | Tests with quantified magic wands.                                                              | ✓               |
| [two-fields.vpr](./two-fields.vpr)                                         | Magic wand with quantifier over two fields.                                                     | ✓               |

Other interesting test cases in the [Silver repository](https://github.com/viperproject/silver/tree/master/src/test/resources) during the development of `MagicWandSnapFunctions` were:
* [wands/examples_paper/conditionals.vpr](https://github.com/viperproject/silver/tree/master/src/test/resources/wands/examples_paper/conditionals.vpr)
* [wands/new_syntax/QPFields.vpr](https://github.com/viperproject/silver/tree/master/src/test/resources/wands/new_syntax/QPFields.vpr)
* [wands/new_syntax/QPPredicates.vpr](https://github.com/viperproject/silver/tree/master/src/test/resources/wands/new_syntax/QPPredicates.vpr)
* [wands/new_syntax/QPWands.vpr](https://github.com/viperproject/silver/tree/master/src/test/resources/wands/new_syntax/QPWands.vpr)
* [wands/new_syntax/SnapshotsNestedMagicWands.vpr](https://github.com/viperproject/silver/tree/master/src/test/resources/wands/new_syntax/SnapshotsNestedMagicWands.vpr)
* [wands/regression/conditionals2.vpr](https://github.com/viperproject/silver/tree/master/src/test/resources/wands/regression/conditionals2.vpr)
* [wands/regression/issue024.vpr](https://github.com/viperproject/silver/tree/master/src/test/resources/wands/regression/issue024.vpr)
* [wands/regression/issue029.vpr](https://github.com/viperproject/silver/tree/master/src/test/resources/wands/regression/issue029.vpr)
