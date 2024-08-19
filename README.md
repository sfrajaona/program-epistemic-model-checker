KHoare: Progam Epistemic Logic to SMT model checker
=========================================

## Tools

1. Haskell compiler GHC. The Glorious Glasgow Haskell Compilation System, version 9.6.4. E.g., from https://www.haskell.org/ghcup/
2. Z3 prover, from https://github.com/Z3Prover/z3 (and optionally CVC5)  
3. Stack from https://www.stackage.org


## Basic usage

### Install the Haskell dependencies by 
``` 
stack init
stack build
```
### Running provided examples with ghci


Run ghci with on the project folder by
```
stack repl
```

On ghci. For each example, load the example file in ghci, so that you can use the functions inside it directly.
```
ghci>:l ExampleCherylsBirthday
--------------------------------


---------------------------------
-- >>> cherylsBirthday
-- Falsifiable. Counter-example:
-- month =  7 :: Integer
-- day   = 16 :: Integer
----------------------------------
-- >>> cherylsBirthdaySat
-- Satisfiable. Model:
-- month =  7 :: Integer
-- day   = 16 :: Integer
---------------------------------
```

## Documentation 
Haddock generated documentation can be accessed at doc/index.html

## References
Rajaona, F., Boureanu, I., Malvone, V., Belardinelli, F. (2023). Program Semantics and Verification Technique for AI-Centred Programs. In: Chechik, M., Katoen, JP., Leucker, M. (eds) Formal Methods. FM 2023. Lecture Notes in Computer Science, vol 14000. Springer, Cham. https://doi.org/10.1007/978-3-031-27481-7_27



