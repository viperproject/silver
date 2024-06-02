# Test Suite for Magic Wand Snap Functions

This folder contains Viper test files that I used when working on MagicWandSnapFunctions for the Silicon project.

## Overview

| Name                       | Description                                                                                     | Expected Result  |
|----------------------------|-------------------------------------------------------------------------------------------------|------------------|
| [test01.vpr](./test01.vpr) | Boolean Magic Wand with trivial LHS                                                             | ✓                |
| [test02.vpr](./test02.vpr) | Integer Magic Wand with trivial LHS                                                             | ✓                |
| [test03.vpr](./test03.vpr) | Integer Magic Wand with LHS = RHS                                                               | ✓                |
| [test04.vpr](./test04.vpr) | Integer Magic Wand with LHS < RHS                                                               | ✓                |
| [test05.vpr](./test05.vpr) | Integer Magic Wand with LHS > RHS                                                               | ✓                |
| [test06.vpr](./test06.vpr) | Applying the magic wand multiple times. Original version leaks information into the outer state | ×                |
| [test07.vpr](./test07.vpr) | Assigning result of applying expression to the same field using booleans                        | ×                |
| [test08.vpr](./test08.vpr) | Assigning result of applying expression to the same field using integers                        | ×                |
| [test09.vpr](./test09.vpr) | Inhaling a magic wand                                                                           | ✓                |
| [test10.vpr](./test10.vpr) | Magic wand with predicates                                                                      | ✓                |
| [test11.vpr](./test11.vpr) | Iterate over a List                                                                             | ✓                |
| [test12.vpr](./test12.vpr) | Applying a quantified magic wand multiple times.                                                | ✓                |
| [test13.vpr](./test13.vpr) | Applying a magic wand multiple times with a quantified expression on the LHS.                   | ✓                |

Other interesting test cases in the [Silver repository](https://github.com/viperproject/silver/tree/master/src/test/resources) during the development of `MagicWandSnapFunctions` were:
* [wands/examples_paper/conditionals.vpr](https://github.com/viperproject/silver/tree/master/src/test/resources/wands/examples_paper/conditionals.vpr)
* [wands/new_syntax/QPFields.vpr](https://github.com/viperproject/silver/tree/master/src/test/resources/wands/new_syntax/QPFields.vpr)
* [wands/new_syntax/SnapshotsNestedMagicWands.vpr](https://github.com/viperproject/silver/tree/master/src/test/resources/wands/new_syntax/SnapshotsNestedMagicWands.vpr)
* [wands/regression/conditionals2.vpr](https://github.com/viperproject/silver/tree/master/src/test/resources/wands/regression/conditionals2.vpr)
* [wands/regression/issue024.vpr](https://github.com/viperproject/silver/tree/master/src/test/resources/wands/regression/issue024.vpr)
* [wands/regression/issue029.vpr](https://github.com/viperproject/silver/tree/master/src/test/resources/wands/regression/issue029.vpr)
