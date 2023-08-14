#![feature(box_patterns)]

use ast::Expr;

use crate::ast::TypeRepr;

/// The abstract syntax tree definition for the programming language, that contains all
/// possible expressions, types, etc..
///
/// It's used to implement the type system.
pub mod ast {
    use std::fmt::Debug;

    /// Represents a location in the abstract syntax tree of this simple
    /// programming language to implement the type system.
    ///
    /// It does hold the line and the column of the location in the source code.
    ///
    /// It's used for simple reporting
    #[derive(Debug, Clone, PartialEq, Eq, Hash)]
    pub struct Location {
        /// The line of the location in the source code.
        pub line: usize,

        /// The column of the location in the source code.
        pub column: usize,
    }

    /// Represents an identifier in the source code, it's used to identify
    /// variables, or type constructors in the context.
    ///
    /// 1. The identifier should always start with an uppercase letter, if it's
    /// a type.
    /// 2. The identifier should always start with a lowercase letter, if it's a
    /// variable.
    ///
    /// The structure wraps `text` and `location`, it's used to be simplier to mock
    /// a location when testing!
    #[derive(Clone, PartialEq, Eq, Hash)]
    pub struct Identifier {
        pub text: String,
        pub location: Option<Location>,
    }

    /// Skips the location, as it is useless when debugging with [`Debug`] trait, we will
    /// already know the location of the identifier, by the context we are printing.
    ///
    /// If we want to print the location, we can use [`Identifier::location`].
    impl Debug for Identifier {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "{}", self.text)
        }
    }

    /// Converts a string into an [`Identifier`] with no location.
    impl From<&str> for Identifier {
        fn from(value: &str) -> Self {
            Self {
                text: value.to_string(),
                location: None,
            }
        }
    }

    /// Represents a type annotation in the abstract syntax tree of this simple
    /// programming language to implement the type system.
    #[derive(Debug, Clone, PartialEq, Eq, Hash)]
    pub enum TypeRepr {
        /// Represents a type constructor with the given identifier.
        ///
        /// 1. The identifier should always start with an uppercase letter or a backtick:
        ///
        /// ## Examples
        ///
        /// ```haskell
        /// 'a, Int, ...
        /// ```
        Constr(Identifier),

        /// Forall quantification of the given identifier to the given type.
        ///
        /// ## Examples
        ///
        /// ```haskell
        /// forall 'a. 'a
        /// ```
        Forall(Identifier, Box<TypeRepr>),

        /// Type function definition of a type to another type.
        ///
        /// ## Examples
        ///
        /// ```haskell
        /// 'a -> 'b
        /// ```
        Fun(Box<TypeRepr>, Box<TypeRepr>),
    }

    /// Represents an expression in this simple programming language to implement
    /// the type system.
    ///
    /// ## Examples
    ///
    /// ```haskell
    /// \x. y
    /// ```
    ///
    /// Etc..
    #[derive(Debug, Clone, PartialEq, Eq, Hash)]
    pub enum Expr {
        /// Represents a number literal with the given value. Just to be easier
        /// to test type system.
        ///
        /// TODO: Maybe adds strings too?
        ///
        /// ## Examples
        ///
        /// ```haskell
        /// ..., -3, -2, -1, 0, 1, 2, 3, ...
        /// ```
        Value(isize),

        /// Represents a binding to variable in the context, identified by the
        /// given identifier.
        ///
        /// ## Examples
        ///
        /// ```haskell
        /// x
        /// ```
        Ident(Identifier),

        /// Type application of the given expression to the given
        /// expressions.
        ///
        /// ## Examples
        ///
        /// ```haskell
        /// x y
        /// ```
        Apply(Box<Expr>, Box<Expr>),

        /// Type annotation of the given expression to the given
        /// type.
        ///
        /// ## Examples
        ///
        /// ```haskell
        /// x : 'x
        /// ```
        Annot(Box<Expr>, TypeRepr),

        /// Lambda abstraction of the given identifier to the given
        /// expression.
        ///
        /// ## Examples
        ///
        /// ```haskell
        /// \x. y
        /// ```
        Abstr(Identifier, Box<Expr>),

        /// Let generalisations of the given identifier to the given
        /// expression.
        ///
        /// ## Examples
        ///
        /// ```haskell
        /// let x = y in z
        /// ```
        Let(Identifier, Box<Expr>, Box<Expr>),
    }
}

/// Language error handling
pub mod error {
    /// Represents a type in the type system of this simple programming language.
    #[derive(Debug, Clone, PartialEq, Eq, Hash)]
    pub struct TypeError {
        pub message: String,
        pub location: Option<crate::ast::Location>,
    }

    /// Creates a type error with the given message.
    ///
    /// NOTE: With location
    #[macro_export]
    macro_rules! infer_error {
        ($dst:expr, $($arg:tt)*) => {
            $crate::error::TypeError {
                message: format!($($arg)*),
                location: $dst.location.clone(),
            }
        };
    }

    /// Creates a type error with the given message.
    ///
    /// NOTE: Without location
    #[macro_export]
    macro_rules! type_error {
        ($($arg:tt)*) => {
            $crate::error::TypeError {
                message: format!($($arg)*),
                location: None,
            }
        };
    }
}

/// The type system tree of this simple programming language.
pub mod typing {
    use std::cell::{Cell, RefCell};
    use std::hash::Hash;
    use std::rc::Rc;

    /// De bruijin level to check the scope of variables.
    pub type Level = usize;

    /// Hole kind of the type system, that can be filled with a type.
    #[derive(Debug, Clone, PartialEq, Eq, Hash)]
    pub enum Hole {
        /// Represents an empty hole, that needs to be filled.
        ///
        /// When you fill in the hole, all its bound variables need to have
        ///   `level < scope`
        Empty(Level),

        /// Represents a filled hole, that has been filled with the given type.
        ///
        /// An important invariant about the scope of holes: it only ever includes
        /// types in the context, never types bound from [`Type::Forall`].
        ///
        /// It's possible to not have this invariant, but it makes everything a *lot*
        /// harder.
        Filled(Type),
    }

    /// Represents a reference to a hole, that can be used to fill it. It does hold
    /// an shared reference to the hole, so it can be filled.
    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct HoleRef {
        /// The mutable reference with reference counting
        pub value: Rc<RefCell<Hole>>,
    }

    impl HoleRef {
        /// Creates a new hole reference with the given hole.
        pub fn new(value: Hole) -> Self {
            Self {
                value: Rc::new(RefCell::new(value)),
            }
        }

        /// Clones the hole reference out of the given hole reference.
        pub fn value(&self) -> Hole {
            self.value.borrow().clone()
        }
    }

    impl Hash for HoleRef {
        fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
            self.value.as_ptr().hash(state);
        }
    }

    /// Represents semantic types in this simple programming language to implement
    /// the type system.
    #[derive(Debug, Clone, PartialEq, Eq, Hash)]
    pub enum Type {
        /// Represents a type constructor with the given identifier.
        ///
        /// 1. The identifier should always start with an uppercase letter.
        ///
        /// ## Examples
        ///
        /// ```haskell
        /// String, Int, ...
        /// ```
        Constr(String),

        /// Represents a type name with the given identifier.
        ///
        /// 1. The identifier should always start with an backtick:
        ///
        /// ## Examples
        ///
        /// ```haskell
        /// 'a, 'b, ...
        /// ```
        Variable(String),

        /// Semantic type application of the given type to the given
        /// types.
        Fun(Box<Type>, Box<Type>),

        /// Forall quantification of the given identifier to the given type.
        Forall(String, Box<Type>),

        /// Debruijn index of the given level, to the given type.
        ///
        /// A type var bound in the context. "Complete and Easy" uses α, β for these
        /// kind of types.
        Bound(Level),

        /// Mutable hole reference
        Hole(HoleRef),
    }

    /// Converts a type representation in the syntax into
    /// a semantic type representation for the type checker.
    ///
    /// Semantic here means that [`Type`] has some meaning and
    /// [`crate::ast::TypeRep`] has only syntax meaning.
    impl From<crate::ast::TypeRepr> for Type {
        fn from(value: crate::ast::TypeRepr) -> Self {
            use crate::ast::TypeRepr::*;

            match value {
                Constr(constr) if constr.text == "Int" => Type::Constr(constr.text),
                Constr(constr) => Type::Variable(constr.text),
                Forall(name, box type_repr) => Type::Forall(name.text, Box::new(type_repr.into())),
                Fun(box domain, box codomain) => {
                    Type::Fun(
                        /* domain   = */ Box::new(domain.into()),
                        /* codomain = */ Box::new(codomain.into()),
                    )
                }
            }
        }
    }

    /// Typing context of the type system, that holds the types of the variables.
    #[derive(Default, Debug, Clone, PartialEq, Eq)]
    pub struct Context {
        /// De Bruijin level of the context.
        pub level: Level,

        /// The number of the current new type variable. It's used
        /// to create new type variables.
        pub counter: Rc<Cell<usize>>,

        /// The names of the variables in the context. This is used for debugging
        /// de bruijin indices.
        pub names: Vec<String>,

        /// The types of the variables in the context.
        pub environment: im_rc::HashMap<String, Type>,
    }
}

/// Debug printing of the type system.
pub mod debug {
    use std::fmt::Debug;

    use crate::typing::*;

    /// Parenthesis macro for debug printing
    ///
    /// This is used to print the type system in a human readable way.
    macro_rules! parens {
        ($p:expr, $dst:expr, $($arg:tt)*) => {
            if $p {
                write!($dst, "(")?;
                write!($dst, $($arg)*)?;
                write!($dst, ")")
            } else {
                write!($dst, $($arg)*)
            }
        };
    }

    /// Debug wrapper for db and semantics
    ///
    /// This is used to print the type system in a human readable way.
    pub struct TypeDebug<'db, 'sema> {
        db: &'db crate::typing::Context,
        sema: &'sema crate::typing::Type,
        parens: bool,
    }

    impl Type {
        /// Creates a new type debug printer.
        pub fn debug<'db, 'sema>(&'sema self, db: &'db Context) -> TypeDebug<'db, 'sema> {
            TypeDebug {
                db,
                parens: false,
                sema: self,
            }
        }

        /// Creates a new type debug printer with parenthesis information.
        ///
        /// This is used to print the type system in a human readable way.
        pub fn debug_all<'db, 'sema>(
            &'sema self,
            parens: bool,
            db: &'db Context,
        ) -> TypeDebug<'db, 'sema> {
            TypeDebug {
                db,
                parens,
                sema: self,
            }
        }

        /// Internal debug function implementation for the types.
        #[inline(always)]
        fn dbg_fmt(&self, p: bool, ctx: &Context, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            match self {
                Type::Variable(name) => write!(f, "'{name}"),
                Type::Constr(constr) => write!(f, "{constr}"),
                Type::Fun(a, b) => {
                    let a = a.debug_all(true, ctx); // Enable forced parenthesis
                    let b = b.debug_all(false, ctx); // Disable parenthesis

                    parens!(p, f, "{a:?} -> {b:?}")
                }
                Type::Forall(name, type_repr) => {
                    let type_repr = type_repr.debug_all(false, ctx); // Disable parenthesis

                    parens!(p, f, "∀ {name}. {type_repr:?}")
                }
                Type::Bound(lvl) => {
                    // Gets the name of the variable from the context
                    let name = ctx
                        .names
                        .get(ctx.level - lvl - 1)
                        .expect("Invalid debruijin index");

                    write!(f, "{name}")
                }
                Type::Hole(hole) => {
                    match hole.value() {
                        Hole::Empty(lvl) => {
                            write!(f, "?{lvl}")
                        }
                        Hole::Filled(type_repr) => {
                            // Print the type representation of the hole
                            type_repr.debug_all(p, ctx).fmt(f)
                        }
                    }
                }
            }
        }
    }

    impl Debug for TypeDebug<'_, '_> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            self.sema.dbg_fmt(self.parens, self.db, f)
        }
    }
}

/// The inference part of the type system of this simple programming language.
pub mod infer {
    use crate::{type_error, typing::*};

    impl Context {
        /// Produces a new context using a new type variable,
        /// using debruijin indexing.
        pub fn create_new_type<S: Into<String>>(self, name: S) -> Context {
            let mut name = name.into();
            let mut ctx = self.clone();
            ctx.level += 1;

            // Concatenates a new ' to the name, until it's not in the context.
            //
            // Like, if you have a variable `x` in the context, it will return `x'`.
            while ctx.names.contains(&name) {
                name.push('\'');
            }

            // Adds the name of the variable to the context.
            ctx.names.push(name);
            ctx
        }

        /// Produces a new context using a new variable.
        ///
        /// This is used for type constructors. Using semantic types.
        ///
        /// NOTE: Semantic types are types that are not the raw AST got from the parser.
        pub fn create_variable(self, name: String, sema: Type) -> Context {
            let mut ctx = self.clone();
            ctx.environment.insert(name, sema);
            ctx
        }

        /// Creates a new fresh name for generalization of a type.
        pub fn new_fresh_variable(&self) -> String {
            self.counter.replace(self.counter.take() + 1);

            // Creates a new type variable with the name `t{counter}`
            //
            // TODO: Convert into the alphabetic letters
            format!("t{}", self.counter.get())
        }

        /// Lookups a type in the contex with the name [`name`].
        ///
        /// If the type is not found, it returns a type error.
        pub fn lookup(&self, name: &str) -> Result<&Type, crate::error::TypeError> {
            self.environment
                .get(name)
                .ok_or_else(|| type_error!("variable `{name}` not found in the context"))
        }
    }
}

/// Substitution part of the type system of this simple programming language.
///
/// Substitution is used to replace type variables with other types creating a new
/// type.
pub mod substitution {
    use crate::typing::{Hole, Type};

    impl Type {
        /// Substitutes a type variable with another type, when it does
        /// match the name.
        ///
        /// Without taking ownership of the type.
        pub fn replace(&mut self, name: &str, replacement: Self) {
            match self {
                Type::Variable(ref constr) if constr == name => {
                    *self = replacement;
                }
                Type::Fun(ref mut domain, ref mut codomain) => {
                    domain.replace(name, replacement.clone());
                    codomain.replace(name, replacement);
                }
                Type::Hole(hole) => {
                    let mut hole_ref = hole.value.borrow_mut();

                    // Get the contents of the hole
                    if let Hole::Filled(type_repr) = &mut *hole_ref {
                        type_repr.replace(name, replacement);
                    }
                }
                // If the bound variable is the same as the name, we don't
                // substitute it.
                Type::Forall(bound, ref mut type_repr) if bound != name => {
                    type_repr.replace(name, replacement);
                }
                _ => {}
            }
        }

        /// Substitutes a type variable with another type, when it does
        /// match the name.
        ///
        /// Taking ownership of the type and creating a new type cloning
        /// the type.
        ///
        /// NOTE: This is a convenience function.
        pub fn substitute(self, name: &str, replacement: Self) -> Self {
            let mut type_repr = self.clone();
            type_repr.replace(name, replacement);
            type_repr
        }
    }
}

/// Let generalization part of the type system of this simple programming language.
///
/// It does create types without holes over all holes in a type.
pub mod generalization {
    use crate::typing::{Context, Hole, HoleRef, Type};

    impl Context {
        /// Instantiates a type with a new type variable.
        ///
        /// Fills the name of forall with a new fresh hole
        pub fn instantiate(&self, name: &str, type_repr: Type) -> Type {
            let new_hole = HoleRef::new(Hole::Empty(self.level));

            type_repr.substitute(name, Type::Hole(new_hole))
        }

        /// Generalises a variable by replacing all holes on it with
        /// a new type variable.
        ///
        /// NOTE: This is used for let generalization, and it's the inverse
        /// of [`Context::instantiate`].
        pub fn generalize(&self, mut type_repr: Type) -> Type {
            // This generalizes over all holes in a type into a list of
            // quantifiers.
            let mut quantifiers = vec![];

            generalize_over(self, &mut quantifiers, &mut type_repr);

            // Since we don't have a list of quantifiers in forall and we have
            // rank-n polymorphism, we can create a spine of forall types.
            //
            // NOTE: This is not the best way to do it, but it's the simplest
            quantifiers
                .into_iter()
                .fold(type_repr, |acc, name| Type::Forall(name, acc.into()))
        }
    }

    /// Generalization implementation, it does takes
    /// a mutable list of quantifiers and a mutable type.
    fn generalize_over(ctx: &Context, quantifiers: &mut Vec<String>, type_repr: &mut Type) {
        match type_repr {
            Type::Fun(ref mut domain, ref mut codomain) => {
                generalize_over(ctx, quantifiers, domain);
                generalize_over(ctx, quantifiers, codomain);
            }
            Type::Forall(_, ref mut type_repr) => {
                generalize_over(ctx, quantifiers, type_repr);
            }
            Type::Hole(hole) => {
                match hole.value() {
                    Hole::Empty(lvl) if lvl > ctx.level => {
                        // Creates a new type variable
                        let new_type_var = ctx.new_fresh_variable();
                        quantifiers.push(new_type_var.clone());

                        // Updates the contents of the hole
                        // with the new type variable.
                        hole.update(Type::Variable(new_type_var));
                    }
                    Hole::Filled(mut type_repr) => {
                        generalize_over(ctx, quantifiers, &mut type_repr);

                        // Updates the contents of the hole
                        // with the new type generalized.
                        hole.update(type_repr);
                    }
                    _ => {}
                }
            }
            _ => {}
        }
    }
}

/// The unification part of the type system of this simple programming language.
pub mod unification {
    use std::rc::Rc;

    use crate::error::TypeError;
    use crate::type_error;
    use crate::typing::{Context, Hole, HoleRef, Level, Type};

    /// Checks if a hole is valid for unification. We need to do the following checks:
    ///
    /// 1. Occurs check: If the variable not occurs in the type, infinite types are impossible.
    /// 2. Level check: If the level of the hole is greater than the level of the context, we can't unify it.
    fn pre_check_hole(hole: HoleRef, scope: Level, sema: Type) -> Result<(), TypeError> {
        match sema {
            Type::Hole(local_hole) if Rc::ptr_eq(&local_hole.value, &hole.value) => {
                return Err(type_error!("occurs check: infinite type"));
            }
            Type::Fun(domain, codomain) => {
                pre_check_hole(hole.clone(), scope, *domain)?;
                pre_check_hole(hole, scope, *codomain)?;
            }
            Type::Forall(_, box type_repr) => {
                pre_check_hole(hole, scope, type_repr)?;
            }
            Type::Hole(local_hole) => {
                // Create a let binding, so we can use it later
                match local_hole.value() {
                    Hole::Empty(lvl) if lvl > scope => {
                        // Updates the contents of the hole
                        // with the new empty hole
                        *local_hole.value.borrow_mut() = Hole::Empty(scope);
                    }
                    Hole::Filled(type_repr) => pre_check_hole(hole, scope, type_repr)?,
                    _ => {}
                }
            }
            _ => {}
        };

        Ok(())
    }

    impl HoleRef {
        /// Fills the content of a hole with a new type.
        ///
        /// It does prechecks on holes before filling them and can return type errors.
        pub fn fill(&self, ctx: &Context, sema: Type) -> Result<(), TypeError> {
            match self.value() {
                Hole::Empty(scope) => {
                    // Checks the hole before filling it, so we can avoid
                    // mismatched levels and infinite types.
                    pre_check_hole(self.clone(), scope, sema.clone())?;

                    // Updates the contents of the hole
                    // with the new type
                    self.update(sema);
                }
                Hole::Filled(type_repr) => unify(ctx, sema, type_repr)?,
            }

            Ok(())
        }

        /// Updates without pre checking the hole.
        #[inline(always)]
        pub fn update(&self, value: Type) {
            *self.value.borrow_mut() = Hole::Filled(value);
        }
    }

    /// Unify two types. Performs equality checks and fills holes.
    ///
    /// It can return type errors.
    pub fn unify(ctx: &Context, sema_a: Type, sema_b: Type) -> Result<(), TypeError> {
        match (sema_a, sema_b) {
            // Hole unification, attributing value
            // to the holes
            (Type::Hole(hole), sema) => hole.fill(ctx, sema)?,
            (sema, Type::Hole(hole)) => hole.fill(ctx, sema)?,

            // Constructor unification
            (Type::Variable(name_a), Type::Variable(name_b)) if name_a == name_b => {}
            (Type::Constr(name_a), Type::Constr(name_b)) if name_a == name_b => {}

            // Function unification
            (Type::Fun(box domain_a, box codomain_a), Type::Fun(box domain_b, box codomain_b)) => {
                unify(ctx, domain_a, domain_b)?;
                unify(ctx, codomain_a, codomain_b)?;
            }

            // Forall unification
            (Type::Forall(a, type_a), Type::Forall(b, box type_b)) => {
                // Alpha equivalence betwhen quantifiers:
                // - `forall 'a. 'a -> 'a` is equivalent to `forall 'b. 'b -> 'b`
                //
                // Because the quantifiers have the same strucutre.
                let ctx = ctx.clone().create_new_type(b.clone());

                let type_a = type_a.clone().substitute(&a, Type::Bound(ctx.level));
                let type_b = type_b.clone().substitute(&b, Type::Bound(ctx.level));

                unify(&ctx, type_a, type_b)?
            }

            // Bound unification
            // If they are the same level, they are the same type.
            (Type::Bound(level_a), Type::Bound(level_b)) if level_a == level_b => {}

            // Reports that don't unifies
            (sema_a, sema_b) => {
                return Err(type_error!(
                    "can not unify two types {:?} and {:?}",
                    sema_a.debug(ctx),
                    sema_b.debug(ctx)
                ))
            }
        };

        Ok(())
    }

    impl Context {
        /// Unifies two types.
        pub fn unify(&self, sema_a: Type, sema_b: Type) -> Result<Type, TypeError> {
            let type_repr = sema_a.clone();
            unify(self, sema_a, sema_b)?;
            Ok(type_repr)
        }
    }
}

/// The subtyping part of the type system of this simple programming language.
///
/// This performs the subtyping relation between two types.
pub mod subsumption {
    use crate::error::TypeError;
    use crate::typing::{Context, Hole, HoleRef, Type};
    use crate::unification::unify;

    /// The direction of the subtyping relation. If it's checking or inferring
    #[derive(Debug, Clone, Copy)]
    enum Direction {
        Left,
        Right,
    }

    /// Performs the subtyping relation between two types.
    ///
    /// # Parameters
    ///
    /// - `direction`: The direction of the subtyping relation. If it's checking or inferring
    /// the left or right side of the relation.
    fn sub_hole(ctx: &Context, hole: HoleRef, sema: Type, dir: Direction) -> Result<(), TypeError> {
        match (hole.value(), dir, sema) {
            // SECTION: Left-side rules:
            //   The left side rules are represented by `:=<` in the paper.
            //
            // Under the context `Γ`, instantiate `^α` type `∀a. A`, with output context `∆`:
            // ```
            //  Γ[^α],β ⊢ ^α :=< B ⊣ ∆,β,∆′
            // ─────────────────────────────────────────────────────────────────── InstLAllR
            //  Γ[^α] ⊢ ^α :=< (∀β.B) ⊣ ∆
            // ```
            (Hole::Empty(_), Direction::Left, Type::Forall(name, box type_repr)) => {
                let ctx = ctx.clone().create_new_type(name.clone());

                sub_hole(&ctx, hole, type_repr, Direction::Left)?;
            }
            // Under the context `Γ`, instantiate `^α` type `A1 -> A2`, with output context `∆`:
            // ```
            //  Γ[^α2,^α1,^α=^α1 → ^α2] ⊢ A1 =<: ^α1 ⊣ Θ    Θ ⊢ ^α2 :=< [Θ]A2 ⊣ ∆
            // ─────────────────────────────────────────────────────────────────── InstLArr
            //  Γ[^α] ⊢ ^α :=< A1 → A2 ⊣ ∆
            // ```
            (Hole::Empty(scope), Direction::Left, Type::Fun(box domain, box codomain)) => {
                let hole_a = HoleRef::new(Hole::Empty(scope));
                let hole_b = HoleRef::new(Hole::Empty(scope));

                hole.update(Type::Fun(
                    /* domain   = */ Type::Hole(hole_a.clone()).into(),
                    /* codomain = */ Type::Hole(hole_b.clone()).into(),
                ));

                // So we invert the direction of the subtyping relation
                sub_hole(ctx, hole_a, domain, Direction::Right)?; // A1 =<: ^α1
                sub_hole(ctx, hole_b, codomain, Direction::Left)?; // ^α2 :=< [Θ]A2
            }

            // SECTION: Right-side rules:
            //   The right side rules are represented by `=<:` in the paper.
            //
            // Under the context `Γ`, instantiate `^α` such that `A <: ^α`, with output context `∆`:
            // ```
            //  Γ[^α],➤^β,^β ⊢ [^β/β]B =<: ^α ⊣ ∆,➤^β,∆′
            // ─────────────────────────────────────────────────────────────────── InstRAllL
            //  Γ[^α] ⊢ (∀β.B) =<: ^α ⊣ ∆
            // ```
            (Hole::Empty(_), Direction::Right, Type::Forall(name, box type_repr)) => {
                let sema = ctx.instantiate(&name, type_repr);

                sub_hole(ctx, hole, sema, Direction::Right)?;
            }
            // Under the context `Γ`, instantiate `^α` such that `A <: ^α`, with output context `∆`:
            // ```
            //  Γ[^α2,^α1,^α=^α1 → ^α2] ⊢ A1 :=< ^α1 ⊣ Θ    Θ ⊢ ^α2 =<: [Θ]A2 ⊣ ∆
            // ─────────────────────────────────────────────────────────────────── InstRArr
            //  Γ[^α] ⊢ A1 → A2 =<: ^α ⊣ ∆
            // ```
            (Hole::Empty(scope), Direction::Right, Type::Fun(box domain, box codomain)) => {
                let hole_a = HoleRef::new(Hole::Empty(scope));
                let hole_b = HoleRef::new(Hole::Empty(scope));

                hole.update(Type::Fun(
                    /* domain   = */ Type::Hole(hole_a.clone()).into(),
                    /* codomain = */ Type::Hole(hole_b.clone()).into(),
                ));

                sub_hole(ctx, hole_a, domain, Direction::Left)?;
                sub_hole(ctx, hole_b, codomain, Direction::Right)?;
            }

            // For everything else, a <: b, only if a = b
            (Hole::Empty(_), _, sema) => hole.fill(ctx, sema)?,

            // Tries to make a subsumption the hole's value with the semantic type
            // `sema`.
            (Hole::Filled(type_repr), _, sema) => {
                sub(ctx, type_repr, sema)?;
            }
        };

        Ok(())
    }

    /// Performs the subtyping relation between two types.
    pub fn sub(ctx: &Context, sema_a: Type, sema_b: Type) -> Result<(), TypeError> {
        match (sema_a, sema_b) {
            // Hole unification, attributing value, it does contains the following rules:
            //
            // ```
            //  α ∌ FV(A)   Γ[^α] ⊢ ^α :=< A ⊣ ∆
            // ────────────────────────────────── <:InstantiateL
            //  Γ[^α] ⊢ ^α <: A ⊣ ∆
            // ```
            (Type::Hole(hole), sema) => sub_hole(ctx, hole, sema, Direction::Left)?,
            // ```
            //  α ∌ FV(A)   Γ[^α] ⊢ A :=< ^α ⊣ ∆
            // ────────────────────────────────── <:InstantiateR
            //  Γ[^α] ⊢ A <: ^α ⊣ ∆
            // ```
            (sema, Type::Hole(hole)) => sub_hole(ctx, hole, sema, Direction::Right)?,

            // Forall subsumtipons, that have the following rules:
            //
            // Under input context `Γ`, type `A` is a subtype of `B`, with output context `∆`:
            // ```
            //  Γ,➤^α,^α ⊢ [^α,α]A <: B ⊣ ∆,➤^α,Θ
            // ──────────────────────────────────── <:∀L
            //  Γ ⊢ (∀a. A) <: B ⊣ ∆
            // ```
            (sema_a, Type::Forall(name, box type_repr)) => {
                // The `➤` symbol means that we are elevating the context, so we can make
                // the type variable "invariant" in the context.
                //
                // Being invariant means that we can't change the type variable's value in context
                // that are not the same context, or contexts that are extending it's context.
                let ctx = ctx.clone().create_new_type(name.clone());

                sub(&ctx, sema_a, type_repr)?;
            }
            //
            // Under input context `Γ`, type `A` is a subtype of `B`, with output context `∆`:
            // ```
            //  Γ,α ⊢ A <: B ⊣ ∆,α,Θ
            // ────────────────────── <:∀R
            //  Γ ⊢ A <: (∀α. B) ⊣ ∆
            // ```
            (Type::Forall(name, box type_repr), sema_b) => {
                let sema_a = ctx.instantiate(&name, type_repr);

                sub(ctx, sema_a, sema_b)?;
            }

            // Function subsumption, its
            // ```
            //  Γ ⊢ B1 <: A1 ⊣ Θ   Θ ⊢ [Θ]A2 <: [Θ]B2 ⊣ ∆
            // ─────────────────────────────────────────── <:→
            //  Γ ⊢ A1 → A2 <: B1 → B2 ⊣ ∆
            // ```
            (Type::Fun(box domain_a, box codomain_a), Type::Fun(box domain_b, box codomain_b)) => {
                sub(ctx, domain_b, domain_a)?;
                sub(ctx, codomain_a, codomain_b)?;
            }

            // For everything else, a <: b, only if a = b
            (a, b) => unify(ctx, a, b)?,
        };

        Ok(())
    }

    impl Context {
        /// Performs the subtyping relation between two types.
        pub fn sub(&self, sema_a: Type, sema_b: Type) -> Result<Type, TypeError> {
            let type_repr = sema_a.clone();
            sub(self, sema_a, sema_b)?;
            Ok(type_repr)
        }
    }
}

/// The mutually recursive type check functions of this simple programming language.
pub mod typer {
    use crate::ast::Expr;
    use crate::type_error;
    use crate::typing::{Context, Hole, HoleRef, Type};

    impl Context {
        /// Checks the type of an expression.
        pub fn check(&self, term: Expr, type_repr: Type) -> Result<(), crate::error::TypeError> {
            match (term, type_repr) {
                // These are the rules marked with `^α`, `^β` and `^γ` in the paper, they are simply
                // holes that need to be filled.
                //
                // The paper use substitution to fill the holes, but we use a different approach
                // that is using mutability, see [`HoleRef`].
                (term, ref type_repr @ Type::Hole(ref hole)) => match hole.value() {
                    Hole::Empty(_) => {
                        let synth = self.infer(term)?;
                        self.sub(synth, type_repr.clone())?;
                    }
                    Hole::Filled(local) => {
                        self.sub(type_repr.clone(), local.clone())?;
                    }
                },
                // Under the context `Γ` with bound name `α`, `e` checks against type `A` with
                // otuput context `Δ`:
                // ```
                //  Γ,α ⊢ e ⇐ A ⊣ ∆,α,Θ
                // ───────────────────── ∀I
                //  Γ ⊢ e ⇐ ∀α. A ⊣ ∆
                // ```
                (term, Type::Forall(name, box type_repr)) => {
                    let bound = Type::Bound(self.level);
                    let ctx = self.clone().create_new_type(name.clone());

                    ctx.check(term, type_repr.substitute(&name, bound))?;
                }
                // Under the context `Γ`, `(λx. e)` checks against type `A → B` with output context
                // `Δ`:
                // ```
                //  Γ,x:A ⊢ e ⇐ B ⊣ ∆,x:A,Θ
                // ───────────────────────── →I
                //  Γ ⊢ (λx. e) ⇐ A → B ⊣ ∆
                // ```
                // NOTE: `x` has type `A`, and `e` has type `B`.
                (Expr::Abstr(name, box expr_e), Type::Fun(box domain, box codomain)) => {
                    let ctx = self.clone().create_variable(name.text, domain);

                    ctx.check(expr_e, codomain)?;
                }
                (Expr::Let(name, box value, box expr), type_repr) => {
                    let expr_type = self.infer(value)?;
                    let ctx = self.clone().create_variable(name.text, expr_type);

                    ctx.check(expr, type_repr)?;
                }
                // Tries the default. a = b, only if a <: b, so the paper presents
                // the following rules:
                //
                // Under the context `Γ`, `()` checks against type `1` and, with output context
                // Γ (the same context).
                // ```
                // ───────────────── 1I
                //  Γ ⊢ () ⇐ 1 ⊣ Γ
                // ```
                //
                // The `()` type can be known in this code as `Int`, they aren't the same of course,
                // but they perform a similar role.
                (term, type_repr) => {
                    self.sub(self.infer(term)?, type_repr)?;
                }
            }

            Ok(())
        }

        /// Synthesizes the type of an expression.
        pub fn infer(&self, term: Expr) -> Result<Type, crate::error::TypeError> {
            match term {
                // Integer axiom, every integer [`isize`] is of type `Int`
                // ```
                // ─────────────────
                //  1, 2, ... : Int
                // ```
                Expr::Value(_) => Ok(Type::Constr("Int".into())),
                // Under the context `Ψ`, a variable `x` is of type `A` if `x` is
                // bound to `A` in `Ψ`:
                // ```
                // (x : A) ∈ Ψ
                // ────────────────────────────
                //  Ψ ⊢ x ⇒ A
                // ```
                Expr::Ident(name) => self.lookup(&name.text).cloned(),
                // Under the context `Ψ`, `e` is the type of `A` and checks against
                // `A`:
                // ```
                //  Ψ ⊢ e ⇒ A
                // ────────────────────────────
                //  Ψ ⊢ (e : A) ⇒ A
                // ```
                Expr::Annot(box expr, type_repr) => {
                    let type_repr = Type::from(type_repr);
                    self.check(expr, type_repr.clone())?;
                    Ok(type_repr)
                }
                // Under the context `Ψ`, applying a function type of `A → C` to
                // `e`, synthesizes type `C`:
                //
                // ```
                //  Ψ ⊢ e ⇐ A
                // ────────────────────────────
                //  Ψ ⊢ A → C • e ⇒⇒ C
                // ```
                Expr::Apply(box f, box arg) => self.apply(self.infer(f)?, arg),
                // ```
                //
                // ────────────────────────────
                //
                // ```
                Expr::Let(name, box value @ Expr::Abstr(_, _), box expr) => {
                    // If it's an abstraction, we should generalize it before
                    // checking the type of the expression
                    let type_rep = self.clone().create_new_type("_").infer(value)?;
                    let expr_type = self.generalize(type_rep);
                    let ctx = self.clone().create_variable(name.text, expr_type);

                    ctx.infer(expr)
                }
                // Under the context `Ψ`, `e` synthesizes type `A` and under the
                // context `Ψ, x : A`, `e′` checks against type `C`:
                // ```
                //  Ψ ⊢ e ⇒ A Ψ, x : A ⊢ e′ ⇐ C
                // ─────────────────────────────
                //  Ψ ⊢ let x = e in e′ ⇐ C
                // ```
                // NOTE: Note the absence of generalization in this rule.
                Expr::Let(name, box value, box expr) => {
                    let expr_type = self.infer(value)?;
                    let ctx = self.clone().create_variable(name.text, expr_type);

                    ctx.infer(expr)
                }
                // Under the context `Ψ`, a lambda abstraction `\x. e` is of type
                // `σ → τ` if `e` is of type `τ` under the context `Ψ, x:σ`:
                // ```
                //  Ψ ⊢ σ → τ   Ψ, x:σ ⊢ e ⇐ τ
                // ────────────────────────────
                //  Ψ ⊢ (\x. e) ⇒ σ → τ
                // ```
                //
                // Or with algorithmic typing rules:
                // ```
                //  Γ,^α,^β,x:^α ⊢ e ⇐ ^β ⊣ ∆,x:^α,Θ
                // ────────────────────────────────── →I⇒
                //  Γ ⊢ (λx.e) ⇒ ^α → ^β ⊣ ∆
                // ```
                Expr::Abstr(name, box expr) => {
                    let domain = Type::Hole(HoleRef::new(Hole::Empty(self.level)));
                    let ctx = self.clone().create_variable(name.text, domain.clone());
                    let codomain = ctx.infer(expr)?;

                    Ok(Type::Fun(domain.into(), codomain.into()))
                }
            }
        }

        /// Applies the type of an expression to another expression.
        ///
        /// It has a weird symbol in "Complete and Easy":
        ///
        /// - `Γ ⊢ A • e ⇒⇒ C ⊣ ∆`: Under input context `Γ`, applying a function of type `A`
        /// to`e` synthesizes type `C`, with output context `∆`
        pub fn apply(&self, f: Type, term: Expr) -> Result<Type, crate::error::TypeError> {
            match f {
                // Under the context `Γ`, `e` checks against type `A`, then under input context Γ,
                // applying a function of type `(A -> C)` to `e` synthesizes type `C`,
                // with output context ∆
                // ```
                //  Γ ⊢ e ⇐ A ⊣ ∆
                // ────────────────────────── →App
                //  Γ ⊢ (A → C) • e ⇒⇒ C ⊣ ∆
                // ```
                Type::Fun(box domain, box codomain) => {
                    self.check(term, domain)?; // e ⇐ A

                    Ok(codomain)
                }

                // Under the context `Γ`, `e` checks against type `A`, then under input context Γ,
                // applying a function of type `(∀α. A)` to `e` synthesizes type `C`, replacing all
                // it's free variables with a new type variable (hole references).
                //
                // Then, under the output context ∆, we can fill the holes with the type of `e`:
                // ```
                //  Γ,^α ⊢ [^α/α]A • e ⇒⇒ C ⊣ ∆
                // ───────────────────────────── ∀App
                //  Γ ⊢ (∀α.A) • e ⇒⇒ C ⊣ ∆
                // ```
                // This rules basically instantiates the forall, and then applies the type, the real
                // rule the rule matching below this one.
                Type::Forall(name, box type_repr) => {
                    self.apply(self.instantiate(&name, type_repr), term)
                }

                // Under the context `Γ`, `e` checks against type `^α1`, then under input context Γ,
                // applying a function of type `^α` to `e` synthesizes type `^α2`, replacing all
                // it's value with a new type variable, then:
                //
                // Under the context `Γ`, applying a function of type `^α` to `e` synthesizes type
                // `^α2`, replacing all it's value with a new type variable, so:
                // ```
                //  Γ[^α2,^α1,^α=^α1 → ^α2] ⊢ e ⇐ ^α1 ⊣ ∆
                // ─────────────────────────────────────── ^αApp
                //  Γ [^α] ⊢ ^α • e ⇒⇒ ^α2 ⊣ ∆
                // ```
                Type::Hole(hole) => {
                    // in this context the variable `hole` is equivalent to `^α`
                    match hole.value() {
                        Hole::Empty(scope) => {
                            let hole_a = HoleRef::new(Hole::Empty(scope));
                            let hole_b = HoleRef::new(Hole::Empty(scope));

                            // ^α=^α1 → ^α2
                            hole.update(Type::Fun(
                                /* domain   = */ Type::Hole(hole_a.clone()).into(),
                                /* codomain = */ Type::Hole(hole_b.clone()).into(),
                            ));

                            self.check(term, Type::Hole(hole_a))?;

                            Ok(Type::Hole(hole_b))
                        }

                        // If the hole is filled, we can apply the type to the expression,
                        // there's a technique called `forcing`, that would be used here,
                        // but it's good for now
                        //
                        // NOTE: Forcing is wrapping any filled hole before start checking,
                        // then we can apply the type to the expression.
                        Hole::Filled(type_repr) => self.apply(type_repr.clone(), term),
                    }
                }

                // There's no rule for applying anything else to an expression, so then, we
                // can return a type error saying that we expected a function type.
                _ => Err(type_error!(
                    "Expected a function type, found {:?}",
                    f.debug(self)
                )),
            }
        }
    }
}

fn main() {
    let ctx = typing::Context::default();

    let type_repr = ctx
        .infer(Expr::Apply(
            /* f  = */
            Expr::Annot(
                /* value = */
                Expr::Abstr(
                    /* name  = */ "f".into(),
                    /* expr  = */
                    Expr::Apply(
                        /* f   = */ Expr::Ident("f".into()).into(),
                        /* arg = */ Expr::Value(10).into(),
                    )
                    .into(),
                )
                .into(),
                /* type_repr = */
                TypeRepr::Fun(
                    /* f      = */
                    TypeRepr::Forall(
                        /* name      = */ "a".into(),
                        /* type_repr = */
                        TypeRepr::Fun(
                            /* domain   = */ TypeRepr::Constr("a".into()).into(),
                            /* codomain = */ TypeRepr::Constr("a".into()).into(),
                        )
                        .into(),
                    )
                    .into(),
                    /* type_repr = */
                    TypeRepr::Constr("Int".into()).into(),
                ),
            )
            .into(),
            /* arg = */ Expr::Abstr("x".into(), Expr::Ident("x".into()).into()).into(),
        ))
        .unwrap();

    println!("{:?}", type_repr.debug(&ctx));
}
