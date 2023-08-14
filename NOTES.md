# Driving Complete and Easy Bidirectional Typechecking for Higher-Rank Polymorphism in Rust

The main goal of this article is making some comments about mb64 implementation of
the [Complete and Easy.. paper](bidir.pdf), but implementing it in pure
rust code with a handwritten parser, and some optimizations, like de bruijin levels and indexes!

## Credits

1. [mb64](https://gist.github.com/mb64/87ac275c327ea923a8d587df7863d8c7#file-tychk_v2-ml)
   for this implementation of "Complete and Easy" paper
2. [Sofia](https://github.com/algebraic-sofia/nuko) for her own implementation of this paper too

## Mentions

1. [Practical type inference for arbitrary-rank types](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/putting.pdf)

## Problems with the paper

1. The paper uses a linked list, which is pretty slow to deal with in real world scenarios, and we should get rid of it.

2. Nominal typing, nominal typing makes harder to unify forall expression, and this tutorial presents an idea
   implementing [debruijin indexes and levels](https://en.wikipedia.org/wiki/De_Bruijn_sequence)

## Required Dependencies

The main dependencies are going to be the crates:

1. [thiserror](https://crates.io/crates/thiserror) for full-featured error handling in rust
2. [im_rc](https://crates.io/crates/im_rc) for immutable data structures with rc
3. [ariadne](https://crates.io/crates/ariadne) for presenting language's errors in the stderr or stdout
4. [fxhash](https://crates.io/crates/fxhash) for a fast hash implementation

## Cool readings

I have made a tutorial about Hindley Milner without any extension, if you don't know anything about type systems, I
highly recommend you to read the following:

1. [My tutorial on Hindley Milner](https://github.com/aripiprazole/ekko/blob/main/docs/3_introduction_to_typing.md)
   which implements [Algorithm W](https://en.wikipedia.org/wiki/Hindley%E2%80%93Milner_type_system) and some another
   useful things for PL theory in Kotlin.
2. [This response on PL theory stackexchange](https://langdev.stackexchange.com/questions/2692/how-should-i-read-type-system-notation/2693#2693)
   which explains important stuff type system's notation

## Bidirectional Type Systems

Bidirectional type checking is a quite popular technique for implementing type systems with complex features, like
Higher-Rank Polymorphism itself, among other features, like Dependent Type Systems. It's constituted of `synthesizing` a
type and, `checking` it against another for comparing two types.

For example, the following expression: `10 : Int`, the number `10` synthesizes the type `Int`, and the type
annotation `checks` the synthesized type `Int` against `Int` specified, and if the wrong type was specified,
like `10 : String`, obviously, `10` can't have type `String`, so the compiler will try to check `10` against `String`,
and fail at this.

## Hindley-Milner

This type checker extends `Hindley-Milner` implementation, I suggest you read
the [Wikipedia's page](https://en.wikipedia.org/wiki/Hindley%E2%80%93Milner_type_system) about hindley milner
implementation.

Our implementation relies on the base of `Algorithm J`, which is mutable and pretty fast, but it's not pure.

The `Hindley-Milner` rules we are going to use are the "generalization" and the "unification", to first, create types
without any type annotation, and second and respectively to check if two types are equal, and if they are not, we should
unify them.

## Higher-Rank Polymorphism

Higher-Rank Polymorphism is a feature that allows us to write polymorphic functions, like the following:

```haskell
let id : ∀ 'a. 'a -> 'a = ... in
let f : (∀ 'a. 'a -> 'a) -> Int = ... in
f id
```

> Pseudo language example

## Unification and Subsumption

Unification is the process of checking if two types are equal, and if they are not, we should unify them, for example,
the following expression: `10 : Int`, the number `10` synthesizes the type `Int`, and the type annotation `checks` the
synthesized type `Int` against `Int` specified, and if the wrong type was specified, like `10 : String`, obviously, `10`
can't have type `String`, so the compiler will try to check `10` against `String`, and fail at this.

But "Subsumption" is another term we are going to use, it's the process of checking if a type is a subtype of another,
and the process is called "polymorphic subtyping", for example, the following expressions:

```haskell
let k : ∀ 'a. ∀ 'b. a -> b -> b = ... in
let f : (Int -> Int -> Int) -> Int = ... in
let g : (∀ 'a. 'a -> 'a) -> Int = ... in
(f k, g k)
```

> Pseudo language example

So, the application `(f k)` is valid in any ML language, or haskell, etc... Because they are the same type when unified,
but when trying to apply `(g k)`, the compiler will try to unify `∀ 'a. 'a -> 'a` with `Int -> Int -> Int`, and fail at
this, so we need to implement the so-called "subsumption".

The type of `∀ 'a. 'a -> 'a` is more "polymorphic" than `∀ 'a. ∀ 'b. a -> b -> b`, so the expressions `f k` and `g k`
should be valid.

## De Bruijin Indexes and Levels

De Bruijin indexes and levels are a way to represent type variables in a type system, for example, the following
expression:

```haskell
let id : ∀ 'a. a -> a = ... in
id 10
```

> The variable `'a` should be replaced by the de bruijin index `0`, which is the first variable in the scope

This technique is used to create rigid type variables in some scopes, like if we have a "hole" of a type, and we
increase the de bruijin level of the scope, we won't be able to substitute the variable with another value in our
internal code, for example, the following expression.

## The algorithm

The algorithm is based on the paper, but with some modifications, like the de bruijin indexes and levels, and some
optimizations, like the `im_rc` crate, which is a immutable data structure with `rc` pointers, and the `fxhash` crate,
which is a fast hash implementation.

The full code implementation is [here](https://github.com/aripiprazole/bidir/blob/main/src/main.rs).

