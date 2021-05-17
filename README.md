# Verified Specifier of S-Graph Language

Verification of a partial evaluation algorithm for S-Graph in Coq. The algorithm was taken from "https://link.springer.com/chapter/10.1007/3-540-57264-3_34"

## Description of Files

##### `utilities.v`
Utility lemmas and tactics. Includes `lia` analogue for ssreflect --
`ssrnatlia`, extracted from https://github.com/amahboubi/lia4mathcomp by Assia
Mahboubi.

##### `substitution.v`
Substitution Theory and basic definitions

##### `int.v`
Interpretation algorithm and its basic properties

##### `dev.v`
Specification algorithm and proof of its correctness 
