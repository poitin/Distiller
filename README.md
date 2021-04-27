# Distiller
Implementation of the distillation algorithm as described in the paper "Distillation: Extracting the Essence of Programs".

The implementation can be built and executed using stack.

The execution is a REPL, with the prompt "POT> " and the following commands:

POT> :help

:load filename          To load the given filename  
:prog                   To print the current program  
:term                   To print the current term  
:eval                   To evaluate the current program  
:distill                To distill the current program  
:quit                   To quit  
:help                   To print this message  

The first thing to do is to load a program file:

POT> :load appapp

This will load the program appapp.pot (the.pot extension is assumed).

To see the contents of this program:

POT> :prog  
main = append (append xs ys) zs;  
append xs ys = case xs of  
                                     Nil -> ys  
                                  | Cons(x,xs) -> Cons(x,append xs ys)  

To see the top-level term:

POT> :term  
append (append xs ys) zs

To apply the distillation transformation to the current program:

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

To evaluate the current program:

POT> :eval

This will prompt for values of the free variables:

xs = [1,2,3]  
ys = [4,5,6]  
zs = [7,8,9]  
[1,2,3,4,5,6,7,8,9]  
Reductions: 101  
Allocations: 8  

To quit from the program:

POT> :quit