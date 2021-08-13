# Distiller
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

