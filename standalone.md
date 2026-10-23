# A Stand-Alone Informalizer for Lean4

Aarne Ranta 2026-10-23


## Goal

Write a stand-alone program that informalizes any piece of Lean code read from standard-in or from a file.
The program should
- call a Lean program that converts Lean to Dedukti
- call RunInformath on the generated Dedukti code with a standard .pgf grammar and .dkgf symbol table
- optionally append a custom .dkgf to the standard symbol table
- output an .html file similar to those in chapters/
- output a help message if asked or if anything goes wrong

It can be a Python or shell script, which calls the other programs.
It should come with an -install option that tries to install them.
If any of the required files (Lean, RunInformath, pgf, dkgf) is missing, it should inform about this.
For anyone that clones this Git repo, it should come together with a package containing these files (maybe made into a release of this repo).

Claude would no more be needed when running this program.


## Deployment

The first way to use it is as a shell program that can be called with `mathlib-informath <opts> <args>` and from std-in containing Lean code.

A second way would be to make it into a web server with an API and a front HTML page, which could first be tested at localhost, later deployd publicly if successful.

A third way would be as a plug-in to VS Code running Lean.



