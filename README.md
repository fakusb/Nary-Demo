# Nary-Demo
Demo of the definitions and tactics to convert between curried and uncurried functions. Most of this are taken from the [coq-bigO library by Armaël Guéneau](https://github.com/fakusb/coq-bigO). [My fork of the whole bigO-library](https://github.com/fakusb/coq-bigO) removed some dependencies, but there still are a lot of unrelated dependencies there.

This repo contains only the general definitions concerning Curried and uncurried functions/definitions and supporting tactics. I changed the tactics a bit to make use of the [smpl plugin](https://github.com/sigurdschneider/smpl.git), but the tactics still do similar stuff as in the full coq-bigO repo.

## Overview
An example for my use case: I have some property `P : forall X, (X -> nat) -> Prop`.
This property is pointwise additive, e.g. `forall X (f1 f2 : X -> nat), P f1 -> P f2  ->  P (fun x => f1 x + f2 x)`.

I can use the definition P on uncurried functions with multiple arguments, e.g. `nat * nat > nat`. But if I use the 'readable' way to state such functions, e.g. `fun '(x,y) => x * 9 + y * x + 9` (instead of `fun (t:nat*nat) => fst t * 9 + snd t * fst t + 9`), I can not apply the additivity-lemma from above. This is because this function is not an abstraction with "+" as head symbol of the body: Instead, `fun '(x,y) => ...` is actually shorthand for `fun t => let (x,y) := tp in ...`, which does not unify with `fun x => _ + _`.

This framework solves this by allowing to transform between uncurried and curried functions, in a way compatible with the implicit destructing binder `fun '(x,y) => ...`. 

The framework can also be used for more complex use cases: For example filters are a mathematical concept that can be defined for types. There are ways to construct a filter for a product type by combining filters on each of the component. As the result is a filter again, lemmas stated on filters apply again, but there is some translation necessary between readable functions and functions usable in lemmas. This advanced use case can be found in all files called `*Nary.v` in the [bigO repo](https://gitlab.inria.fr/agueneau/coq-bigO/-/tree/master/src).


## Detailed Overview
- [theories/GenericNary.v](theories/GenericNary.v) contains the framework itself:
    - A function `Rarrow domain range` that produces the type of curried functions taking the arguments from the list domain and returning the type range. (`Rarrow : list Type -> Type -> Type` with e.g. `Rarrow [nat;bool,unit] Z  =  nat -> bool -> unit -> Z`).
    - A function `RTuple domain` that produces the tuple type for the given list (`Rtuple : list Type -> Type` with e.g. `Rtuple [nat;bool;unit] nat * bool * unit`)).
    - A way to Curry a function: `Fun' : forall (domain : UPlist Type) (range : Type), (Rtuple domain -> range) -> Rtuple domain -> range`
    - A way to uncurry a function : `App : forall (domain : UPlist Type) (range : Type), Rarrow domain range -> Rtuple domain -> range`
    - Tactics to generate the "right" list of types (`domain`) for a given function f, as unification of coq is not strong enough to infer this list. (In general, this can also be used for more complex cases, e.g. in the case of filters in coq-bigO, a list of filters is found for each function argument.)

My case study is the relation `leUpToC f g`, written `f <=c g`, of type `\forall X (f g : X -> nat), Type`<sup>1</sup>. It states that `f` is less than  `g` up to a multiplicative factor, e.g. there exists some constant c such that `forall x, f x <= c * g x`. We define it and it's properties only on a single argument and later introduce tactics and lemmas to support multi-argument functions:
- [theories/UpToC.v](theories/UpToC.v) does not need to know about `genericNary.v` and contains: 
    - The relation itself.
    - Several lemmas on this relation which are proven for the 1-argument-definition, e.g.. :
        - `f1 <=c F  ->  f2 <=c F  ->  (fun x => f1 x + f2 x) <=c F.`
        - `f <=c F  ->  (fun x => c * f1 x ) <=c F.`
    - The tactics `smpl_upToC` (and `smpl_upToC_solve`) that try to use the lemmas in a safe (and unsafe) way to show e.g.
    - `(fun x : nat => 3 * x + 10) <=c (fun x : nat => x + 1)` (examples at end of file)
    - (unrelated to the Curry/Uncurry aspect): A type class `UpToC` that wraps the existence of some function in some "leUpToC-Class" and allows for lemmas as:
  
        There is some function `f : nat -> nat` which is `<=c (fun x => x+1)` and fulfils a certain property:
    
        ``` coq 
         { f : UpToC (fun x => x + 1) | forall x, 3 * x + 10 <= f x}`
     
- [theories/UpToCNary.v](theories/UpToCNary.v) now contains the lifting to multiple arguments:

    - The lemmas must be written in a certain style which mechanically follows from the statements for arity 1:
      ```
      Lemma upToC_add_nary (domain : UPlist Type) F (f1 f2 : Rarrow domain nat) :
        Uncurry f1 <=c F
         -> Uncurry f2 <=c F
         -> Fun' (fun x => App f1 x + App f2 x) <=c F.
      They are shown automatically by the tactic `prove_nary` using the lemma for arity 1.
    - They can be applied using the "nary apply" tactic from `GenericNary.v`, which inferes<sup>2</sup> the right `domain`, applies the lemma, and tidies up the resulting goal.
    - I then add these new lemmas to the smpl database to extend the tactic support from `UpToC.v`, i.e. to solving goals of form `(fun '(x,y,z) => ...) <=c (fun '(x,y,z) => ...)`. See the examples at the end of this file.
    
<sup>1</sup>: For my use case, it makes sense to define this relation in `Type` instead of `Prop`, as it allows to project out the constant. This means that the example code has to go through some hoops to e.g. rewrite in `Type` instead of `Prop` by using the Type-copy of the setoid rewrite machinery (i.e. the modules `CMorphisms`,... instead of `Morphisms`,... )

<sup>2</sup>: Actually, one has to extend the tactic for each intended predicate using the `domain_of_goalauto` hint database.

## How to build

### Required packages

You need `8.8.2`.

### Build external libraries

The demo depends on external libraries. Initialise and build them once as follows:

``` sh
  git submodule init
  git submodule update
  make deps

### Building the demo

- `make all` builds the library
- `make html` generates clickable coqdoc `.html` in the `website` subdirectory
- `make clean` removes all build files in `theories` and `.html` files in the `website` directory
- `make realclean` also removes all build files in the `external` directory. You have to run `make deps` again after this.
