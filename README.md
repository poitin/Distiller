# Distiller ![Build status](https://github.com/YaccConstructor/Distiller/actions/workflows/haskell.yml/badge.svg)

Implementation of the distillation algorithm as described in the paper ["Distillation: Extracting the Essence of Programs"](https://dl.acm.org/doi/10.1145/1244381.1244391).

The implementation can be built and executed using stack.

## Execution 
The execution is a REPL, with the prompt "POT> " and the following commands:

```
POT> :help

:load <filename>        To load the given filename  
:prog                   To print the current program  
:term                   To print the current term  
:eval                   To evaluate the current program  
:distill <filename>     To distill the current program. If the file name is provided, the result will be stored in the specified file.  
:quit                   To quit  
:help                   To print this message  
```
The first thing to do is to load a program file:

```
POT> :load nrev
```

This will load the program nrev.pot (the.pot extension is assumed).

To see the contents of this program:

```
POT> :prog  
main = nrev xs;
append xs ys = case xs of
                  Nil -> ys
                | Cons(x,xs) -> Cons(x,append xs ys);
nrev xs = case xs of
             Nil -> []
           | Cons(x,xs) -> (append (nrev xs) [x])  
```

To see the top-level term:

```
POT> :term  
nrev xs
```

To apply the distillation transformation to the current program:
```
POT> :distill  
main = case xs of
          Nil -> []
        | Cons(x,xs) -> (f xs x []);
f xs' x x'' = case xs' of
                 Nil -> Cons(x,x'')
               | Cons(x',xs) -> (f xs x' Cons(x,x''))  
```

To evaluate the current program:
```
POT> :eval
```
This will prompt for values of the free variables:

```
xs = [1,2,3,4,5,6,7,8,9]
[9,8,7,6,5,4,3,2,1]
Reductions: 118
Allocations: 10  
```

To quit from the program:

```
POT> :quit
```

## Experiments
Matrices used for experiments, stored in `Matrices.pot` file in special format and can be found via the [link](https://github.com/YaccConstructor/Distiller/blob/d2e813f844e61916007d45195abfd8ccfeb8fd67/examples/Matrices.pot#L7). 
Links to original matrices definition are shown in the following table:
| Matrix ID | Matrix | Number of non-zero elements |
|----|---------|-----|
| 1 | https://sparse.tamu.edu/Pajek/football | 118 |
| 2 | https://sparse.tamu.edu/Pajek/GD99_b | 252 |
| 3 | https://sparse.tamu.edu/Pajek/Cities | 1,342 |
| 4 | https://sparse.tamu.edu/JGD_Forest/TF11 | 1,607 |
| 5 | https://sparse.tamu.edu/Pajek/GD96_a | 1,677 |
| 6 | [bottom triangle matrix of size 2048\*2048 ](https://github.com/YaccConstructor/Distiller/blob/d2e813f844e61916007d45195abfd8ccfeb8fd67/examples/Matrices.pot#L33), [bottom triangle matrix of size 64\*64](https://github.com/YaccConstructor/Distiller/blob/d2e813f844e61916007d45195abfd8ccfeb8fd67/examples/Matrices.pot#L38)| -- |


The next operations with free variables `m1`, `m2`, `m3`, `msk` and operators `mAdd`, `kron`, `mask` were investigated:
|Operation | Definition|
|----------|-----------|
| E-wise successive additions | `mAdd (not) (or) (mAdd (not) (or) (m2) (m3)) (m1)` |
| Kronecker with masking | `kron (not) (or) (mask (m1) (msk)) (m2)` |

The following metrics were obtained from experiments:
| Function | Input | Size  | Reductions (original/distilled)| Allocations (original/distilled)| Link |
|----------|-------|-------------------------|----------------------|-----------------------|-----------------|
| Kronecker with masking | (1), (2), (6) | 64 | 535125/367868 | 92470/67110 | [Original program](https://github.com/YaccConstructor/Distiller/blob/3340108d7138d4f663d921f883e31b880107c677/examples/KronMask.pot#L5), [distilled program](https://github.com/YaccConstructor/Distiller/blob/3340108d7138d4f663d921f883e31b880107c677/examples/KronMaskDistilled.pot#L6)|
| Kronecker with masking | (1), (4), (6) | 2048 | 1215051/827020 | 212133/151601 | [Original program](https://github.com/YaccConstructor/Distiller/blob/3340108d7138d4f663d921f883e31b880107c677/examples/KronMask.pot#L5), [distilled program](https://github.com/YaccConstructor/Distiller/blob/3340108d7138d4f663d921f883e31b880107c677/examples/KronMaskDistilled.pot#L6) |
| E-wise successive additions | (1), (2), (3) | 64 | 20317/11459 | 3170/2372 |[Original program](https://github.com/YaccConstructor/Distiller/blob/3340108d7138d4f663d921f883e31b880107c677/examples/MAdds.pot#L5), [distilled program](https://github.com/YaccConstructor/Distiller/blob/3340108d7138d4f663d921f883e31b880107c677/examples/MAddsDistilled.pot#L5)|
| E-wise successive additions | (1), (2) | 64 | 11900/5811 | 2007/1429 |[Original program](https://github.com/YaccConstructor/Distiller/blob/3340108d7138d4f663d921f883e31b880107c677/examples/MAdds.pot#L5), [distilled program](https://github.com/YaccConstructor/Distiller/blob/3340108d7138d4f663d921f883e31b880107c677/examples/MAddsDistilled.pot#L5)|
| E-wise successive additions | (1) | 128 |  16644/6464 |3170/1921 |[Original program](https://github.com/YaccConstructor/Distiller/blob/3340108d7138d4f663d921f883e31b880107c677/examples/MAdds.pot#L5), [distilled program](https://github.com/YaccConstructor/Distiller/blob/3340108d7138d4f663d921f883e31b880107c677/examples/MAddsDistilled.pot#L5)|
| E-wise successive additions | (2), (4) | 2048 | 139851/81907 | 20351/15056 |[Original program](https://github.com/YaccConstructor/Distiller/blob/3340108d7138d4f663d921f883e31b880107c677/examples/MAdds.pot#L5), [distilled program](https://github.com/YaccConstructor/Distiller/blob/3340108d7138d4f663d921f883e31b880107c677/examples/MAddsDistilled.pot#L5)|
