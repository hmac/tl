use ./not/a/path as nope

main: Int { nope.nopey }
---
Error:

   1: use ./not/a/path as nope
          ^^^^^^^^^^^^^
           no file matches this import path
