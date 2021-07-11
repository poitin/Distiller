# Distiller
Implementation of the distillation algorithm as described in the paper ["Distillation: Extracting the Essence of Programs"](https://dl.acm.org/doi/10.1145/1244381.1244391).

The implementation can be built and executed using stack.

## Execution 
The execution is a REPL, with the prompt "POT> " and the following commands:

```
POT> :help

:load filename          To load the given filename  
:prog                   To print the current program  
:term                   To print the current term  
:eval                   To evaluate the current program  
:distill <filename>     To distill the current program. If the file name provided, the distillation result will be stored in the specified file.  
:quit                   To quit  
:help                   To print this message  
```
The first thing to do is to load a program file:

```
POT> :load appapp
```

This will load the program appapp.pot (the.pot extension is assumed).

To see the contents of this program:

```
POT> :prog  
main = append (append xs ys) zs;  
append xs ys = case xs of  
                    Nil -> ys  
                  | Cons(x,xs) -> Cons(x,append xs ys)  
```

To see the top-level term:

```
POT> :term  
append (append xs ys) zs
```

To apply the distillation transformation to the current program:
```
POT> :distill  
main = f xs ys zs;  
f xs ys zs = case xs of  
                  Nil -> case ys of  
                              Nil -> zs  
                            | Cons(x,xs) -> Cons(x,f' xs zs)  
                | Cons(x,xs) -> Cons(x,f xs ys zs);  
f' xs' zs = case xs' of  
                 Nil -> zs  
               | Cons(x,xs) -> Cons(x,f' xs zs)  
```

To evaluate the current program:
```
POT> :eval
```
This will prompt for values of the free variables:

```
xs = [1,2,3]  
ys = [4,5,6]  
zs = [7,8,9]  
[1,2,3,4,5,6,7,8,9]  
Reductions: 101  
Allocations: 8  
```

To quit from the program:

```
POT> :quit
```

## Experiments
The following matrices were used in the experiments:
| ID | Matrice |
|----|---------|
| 1 | https://sparse.tamu.edu/Pajek/football |
| 2 | https://sparse.tamu.edu/Pajek/GD99_b |
| 3 | https://sparse.tamu.edu/Pajek/Cities |
| 4 | https://sparse.tamu.edu/JGD_Forest/TF11 |
| 5 | https://sparse.tamu.edu/Pajek/GD96_a |
|6 | https://sparse.tamu.edu/JGD_Homology|
| 7 | triangle matrice |
The next operations with free variables `m1`, `m2`, `m3`, `msk` and operators `mAdd`, `kron`, `mask` and were investigated:
|Operation | Definition|
|----------|-----------|
| E-wise successive additions | `mAdd isZ (or) (mAdd isZ (or) (m2) (m3)) (m1)` |
| Kronecker with masking | `kron isZ (or) (mask (m1) (msk)) (m2)` |

The following metrics were obtained from experiments:
| Function | Input | # of non-zero matrices  | Reductions (original/distilled)| Allocations (original/distilled)| Link |
|----------|-------|-------------------------|----------------------|-----------------------|-----------------|
| Kronecker with masking | (1), (2), (7) | 64 | 535125/367868 | 92470/67110 | - |
| Kronecker with masking | (1), (4), (7) | 2048 | 1215051/827020 | 212133/151601 | - |
| E-wise successive additions | (1), (2), (3) | 64 | 17990/10520 | 2517/1979 |-----------------|
| E-wise successive additions | (1), (2) | 64 | 11904/6397 | 2007/1613 | -- |
| E-wise successive additions | (6) | 128 |  16648/6464 |3170/1921 | -- |
| E-wise successive additions | (2), (4) | 2048 | 106411/66272 | 11759/9849 | -- |