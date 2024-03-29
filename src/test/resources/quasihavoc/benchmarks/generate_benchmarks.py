#! /usr/bin/python3

from pathlib import Path
import os

script_file = Path(__file__).resolve()
# we are currently in silicon/src/test/resources/quasihavoc/benchmarks
top_dir = script_file.parent
os.chdir(top_dir)
os.makedirs('autogen', exist_ok=True)

from string import Formatter
from collections import namedtuple

arg = namedtuple("arg", ["name", "type"])

class testcase:
    def __init__(self, prelude, methods):
        self.prelude = prelude
        self.methods = methods

    def write(self, fname, n):
        havoc_filename = f"autogen/{fname}_havoc_{n}.vpr"
        alt_filename = f"autogen/{fname}_alt_{n}.vpr"

        with open(havoc_filename, "w") as f:
            f.write(self.prelude)
            for m in self.methods:
                f.write(m.write(True, n))

        with open(alt_filename, "w") as f:
            f.write(self.prelude)
            for m in self.methods:
                f.write(m.write(False, n))

class writer():
    def __init__(self):
        self.output = "// !!! AUTOGENERATED !!!\n"
        self.indent_level = 0
    
    def write(self, s):
        self.output += s
    
    def newline(self):
        self.output += "\n"

    def indent(self):
        self.indent_level += 1

    def unindent(self):
        self.indent_level -= 1

    def write_line(self, s):
        self.output += "\t"*self.indent_level + s + "\n"

class method:
    def __init__(self, args, requires, havoc_body, alt_body, name="foo"):
        self.args = args
        self.requires = requires
        self.havoc_body = havoc_body
        self.alt_body = alt_body
        self.name = name

    def write(self, havoc, n):

        w = writer()

        method_name = f"{self.name}_{'havoc' if havoc else 'other'}"
        w.write(f"method {method_name}(")

        # Write the arugments
        str_args = []
        for arg in self.args:
            str_arg_names = self.expand_fs(arg.name, n)
            str_args += [f"{a}: {arg.type}" for a in str_arg_names]

        w.write(', '.join(str_args))
        w.write(')')
        w.newline()

        # Write the requires
        w.indent()
        for require in self.requires:
            for str_req in self.expand_fs(require, n):
                w.write_line("requires " + str_req)
        w.unindent()

        # Write the body
        w.write_line("{")
        w.indent()

        body = self.havoc_body if havoc else self.alt_body
        for stmt in body:
            for line in self.expand_fs(stmt, n):
                w.write_line(line)

        w.unindent()
        w.write_line("}")

        return w.output
            

    def expand_fs(self, s, n):
        # Check if it's a format string
        if len([t for t in Formatter().parse(s) if t[1] is not None]) >= 1:
            return [s.format(i) for i in range(n)]
        else:
            return [s]

########################
# alias_test.py

prelude = """
field f: Int
"""

args = [arg("y", "Ref"), arg("z", "Ref"), arg("x{0}", "Ref")]
requires = [
    "acc(y.f) && y.f == 3",
    "acc(z.f) && z.f == 4",
    "x{0} == y || x{0} == z",
]

common_body = [
    "//:: ExpectedOutput(assert.failed:assertion.false)",
    "assert y.f == 3",
]

body = ["quasihavoc x{0}.f"] + common_body
alt_body = ["exhale acc(x{0}.f); inhale acc(x{0}.f)"] + common_body

alias_method = method(args, requires, body, alt_body)
alias_test = testcase(prelude, [alias_method])

##########################
# impl_test.py

prelude = """
field f: Int
"""

args = [arg("y", "Ref"), arg("x{0}", "Ref")]
requires = ["acc(y.f) && y.f == 42"]

common_body = [
    "assume y != x{0}",
    "assert y.f == 42",
]

havoc_body = ["quasihavoc y == x{0} ==> y.f"] + common_body
alt_body = ["exhale y == x{0} ==> acc(y.f); inhale y == x{0} ==> acc(y.f)"] + common_body

impl_method = method(args, requires, havoc_body, alt_body)
impl_test = testcase(prelude, [impl_method])

#######################
# quasihavocall_test.py

prelude = """
field f: Int
"""

args = [arg("x", "Ref"), arg("s", "Set[Ref]")]
requires = ["forall z: Ref :: z in s ==> acc(z.f) && z.f == 42",
            "x in s"]


havoc_body = ["quasihavocall z: Ref :: z in s && z != x ==> z.f // {0}"]
alt_body = ["exhale forall z: Ref :: z in s && z != x ==> acc(z.f); inhale forall z: Ref :: z in s && z != x ==> acc(z.f) // {0}"]

common_body = [
    "assert x.f == 42"
]

havocall_method = method(args, requires, havoc_body + common_body, alt_body + common_body)
havocall_test = testcase(prelude, [havocall_method])


########################
# havocall_no_cond.py

prelude = """
field f: Int
field g: Int
method ___silicon_hack407_havoc_all_Pred()

predicate Pred(x: Ref) {
    acc(x.f) && x.f >= 0
}
"""

args = [arg("x", "Ref")]

requires = ["Pred(x)"]

havoc_body = ["quasihavocall z: Ref :: Pred(z) // {0}"]
alt_body = ["___silicon_hack407_havoc_all_Pred() // {0}"]

havocall_no_cond_method = method(args, requires, havoc_body, alt_body)
havocall_no_cond_test = testcase(prelude, [havocall_no_cond_method])

#########################
# havocall_sets.py

prelude = """
field f: Int
"""

args = [arg("x", "Ref"), arg("s{0}", "Set[Ref]"), arg("t", "Set[Ref]")]

requires = ["forall z: Ref :: z in s{0} ==> acc(z.f)",
            "forall z: Ref :: z in t ==> acc(z.f)",
            "x in s{0} ==> x.f == 42",
            "x in t ==> x.f == 43",
]

havoc_body = ["quasihavocall z: Ref :: z in s{0} ==> z.f"]
alt_body = ["exhale forall z: Ref :: z in s{0} ==> acc(z.f); inhale forall z: Ref :: z in s{0} ==> acc(z.f)"]

common_body = ["assume !(x in s{0})",
               "assume x in t",
               "assert x.f == 43"]


havocall_sets_method = method(args, requires, havoc_body + common_body, alt_body + common_body)
havocall_sets_test = testcase(prelude, [havocall_sets_method])

#########################
# havoc fractions

prelude = """
field f: Int
"""

args = [arg("y", "Ref"), arg("x{0}", "Ref"), arg("z", "Ref"), arg("pz", "Perm")]

requires = [
    "acc(x{0}.f, 1/1000)",
    "acc(z.f, 1/1000) && z.f == 1234",
]

havoc_body = ["quasihavoc y.f"]
alt_body = ["label L; var py: Perm := perm(y.f); exhale acc(y.f, py); inhale acc(y.f, py)"]

common_body = [
    "assume y == x{0}",
    "assume y == z",
    "//:: ExpectedOutput(assert.failed:assertion.false)",
    "assert z.f == 1234     // should fail",
]

havoc_fracs_method = method(
    args,
    requires,
    havoc_body + common_body,
    alt_body +  common_body
)
havoc_fracs_test = testcase(prelude, [havoc_fracs_method])


########################
# Output the tests

for i in range(3, 11):
    alias_test.write("alias_test", i)
    impl_test.write("impl_test", i)

for i in range(10, 100, 10):
    havocall_test.write("havocall_test", i)
    havocall_no_cond_test.write("no_cond", i)

for i in range(10, 20):
    havocall_sets_test.write("sets_test", i)

for i in range(3, 16):
    havoc_fracs_test.write("havoc_fracs", i)
