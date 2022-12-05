#!/usr/bin/python

import os
import re
import sys
import shutil
import subprocess

class Section(object):

    def __init__(self, name, begin, end):
        super(Section, self).__init__()

        self.re_begin = begin
        self.re_end = end
        self.name = name

    def starts(self, line):
        return re.match(self.re_begin, line)

    def ends(self, line):
        return re.match(self.re_end, line)

class AnnotatedSection(Section):

    def __init__(self, name):
        super(AnnotatedSection, self).__init__(
            name,
            re.compile(r"^\s*\\\* BEGIN {}$".format(name)),
            re.compile(r"^\s*\\\* END {}$".format(name))
        )

class Parser(object):

    def __init__(self):
        super(Parser, self).__init__()

        self.lines = []

        self.sections = {}
        self.active_sections = []

        self.has_task_enabled = False

        for section in ["TRANSLATION", "PROCVARS", "FAIRNESS"]:
            self.sections[section] = AnnotatedSection(section)

        self.sections["VARIABLES"] = Section(
            "VARIABLES",
            re.compile(r"^VARIABLES.*$"),
            re.compile(r"^$")
        )
        self.sections["SPEC"] = Section(
            "SPEC",
            re.compile(r"^Spec == .*$"),
            re.compile(r"^$")
        )

        self.section_lines = {section : [] for section in self.sections}

    def update_section(self, line):
        for section in self.sections.itervalues():

            if section.starts(line):
                self.active_sections.append(section.name)
                # Create a new list for each section we encounter
                if "TRANSLATION" in self.active_sections:
                     self.section_lines[section.name].append([])

            elif section.ends(line) and section.name in self.active_sections:
                assert self.active_sections[-1] == section.name, \
                       "mismatched section ending for {}".format(section.name)

                # Ensure section ending is also added
                if "TRANSLATION" in self.active_sections:
                      self.section_lines[self.active_sections[-1]][-1].append(line)

                self.active_sections.pop()

    def skip(self, line):
        if ("PROCVARS" in self.active_sections and
            not self.sections["PROCVARS"].starts(line)):
            return True

        if ("FAIRNESS" in self.active_sections and
            not self.sections["FAIRNESS"].starts(line)):
            return True

        return False

    def parse(self, line):
        self.update_section(line)

        if self.skip(line):
            return

        if "TaskEnabled(self)" in line:
            self.has_task_enabled = True

        if "TRANSLATION" in self.active_sections:
            if len(self.active_sections) > 1:
                # We're in a section within the translation, record the line
                self.section_lines[self.active_sections[-1]][-1].append(line)
            else:
                # We're within the translation, append the context switch
                # enabling condition
                if self.has_task_enabled:
                    line = re.sub(r"(pc\[self\] = \"\w+\"$)", r"\1 /\\ TaskEnabled(self)", line)

            self.lines.append(line)

        elif "PROCVARS" in self.active_sections:
            # proc vars are the second VARIABLES statement
            # Also, get rid of ending matching line
            procvar_lines = self.section_lines["VARIABLES"][1][:-1]
            procvar_lines[0] = procvar_lines[0].replace("VARIABLES ", "proc_vars == <<")
            procvar_lines[-1] = procvar_lines[-1].rstrip() + ">>\n"

            # Keep the delimiter
            self.lines.append(line)

            for l in procvar_lines:
                self.lines.append(l)

        elif "FAIRNESS" in self.active_sections:
            # Get rid of start & end matching lines
            fairness_lines = self.section_lines["SPEC"][0][1:-1]

            # Keep the delimiter
            self.lines.append(line)

            for l in fairness_lines:
                self.lines.append(l)

        else:
            self.lines.append(line)

input_file = sys.argv[-1]
parser = Parser()

if not os.path.exists(input_file):
    raise RuntimeError("Couldn't find {}".format(input_file))

# Transpile to TLA+
subprocess.call("java pcal.trans {}".format(input_file), shell=True)

# Tweak the transpiled bits
with open(input_file, "r") as fh:
    for line in fh:
        parser.parse(line)

with open(input_file, "w") as fh:
    fh.writelines(parser.lines)
