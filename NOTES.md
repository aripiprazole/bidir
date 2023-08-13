# Driving Complete and Easy Bidirectional Typechecking for Higher-Rank Polymorphism in Rust

The main goal of this article is making accessible the [Complete and Easy.. paper](bidir.pdf), implementing it in pure rust code with a handwritten parser, and some optimizations, like de bruijin levels and indexes!

## Credits

1. [mb64](https://gist.github.com/mb64/87ac275c327ea923a8d587df7863d8c7#file-tychk_v2-ml)
   for their implementation of this paper
2. [Sofia](https://github.com/algebraic-sofia/nuko) for her own implementation of this paper too

## Problems with the paper

1. The paper uses a linked list, which is pretty slow to deal with in real world scenarios, and we should get rid of it.

2. Nominal typing, nominal typing makes harder to unify forall expression, and this tutorial presents an idea implementing [debruijin indexes and levels](https://en.wikipedia.org/wiki/De_Bruijn_sequence)

## Required Dependencies

The main dependencies are going to be the crates:

1. [thiserror](https://crates.io/crates/thiserror) for full featured error handling in rust
2. [ariadne](https://crates.io/crates/ariadne) for presenting language's errors in the stderr or stdout
3. [fxhash](https://crates.io/crates/fxhash) for a fast hash implementation

## Cool readings

I have made a tutorial about Hindley Milner without any extension, if you don't know anything about type systems, I highly recommend you to read the following:

1. [My tutorial on Hindley Milner](https://github.com/aripiprazole/ekko/blob/main/docs/3_introduction_to_typing.md) which implements [Algorithm W](https://en.wikipedia.org/wiki/Hindley%E2%80%93Milner_type_system) and some another useful things for PL theory in Kotlin.
2. [This response on PL theory stackexchange](https://langdev.stackexchange.com/questions/2692/how-should-i-read-type-system-notation/2693#2693) which explains important stuff type system's notation

## Bidirectional Type Systems

Bidirectional type checking is a quite popular technique for implementing type systems with complex features, like Higher-Rank Polymorphism itself, among other features, like Dependent Type Systems. It's constituted of `synthesizing` a type and, `checking` it against another for comparing two types.

For example, the following expression: `10 : Int`, the number `10` synthesizes the type `Int`, and the type annotation `checks` the synthesized type `Int` against `Int` specified, and if the wrong type was specified, like `10 : String`, obviously, `10` can't has type `String`, so the compiler will try to check `10` against `String`, and fail at this.
