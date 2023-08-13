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
        /// 1. The identifier should always start with an uppercase letter.
        ///
        /// ## Examples
        ///
        /// ```haskell
        /// A
        /// ```
        Constr(Identifier),

        /// Forall quantification of the given identifier to the given type.
        ///
        /// ## Examples
        ///
        /// ```haskell
        /// forall A. A
        /// ```
        Forall(Identifier, Box<TypeRepr>),

        /// Type function definition of a type to another type.
        ///
        /// ## Examples
        ///
        /// ```haskell
        /// A -> B
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
        /// x : Y
        /// ```
        Annot(Box<Expr>, Box<TypeRepr>),

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
    use std::{
        cell::{Cell, RefCell},
        hash::Hash,
        rc::Rc,
    };

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
        /// 1. The identifier should always start with an uppercase letter.
        ///
        /// ## Examples
        ///
        /// ```haskell
        /// A, B, ...
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
                Constr(constr) => Type::Variable(constr.text),
                Forall(name, type_repr) => Type::Forall(name.text, Box::new((*type_repr).into())),
                Fun(domain, codomain) => {
                    Type::Fun(
                        /* domain   = */ Box::new((*domain).into()),
                        /* codomain = */ Box::new((*codomain).into()),
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
            p: bool,
            db: &'db Context,
        ) -> TypeDebug<'db, 'sema> {
            TypeDebug {
                db,
                parens: p,
                sema: self,
            }
        }

        /// Internal debug function implementation for the types.
        #[inline(always)]
        fn dbg_fmt(&self, p: bool, ctx: &Context, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            match self {
                Type::Variable(name) => write!(f, "'{name}"),
                Type::Constr(constr) => write!(f, "'{constr}"),
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
                    let hole_ref = hole.value.borrow();

                    // Get the contents of the hole
                    match &*hole_ref {
                        Hole::Empty(lvl) => {
                            write!(f, "?{lvl}")
                        }
                        Hole::Filled(type_repr) => {
                            // Clone so we can drop the borrow to the hole
                            //
                            // NOTE: We drop the hole, so we don't have two borrows
                            // to the same hole.
                            let type_repr = type_repr.clone();
                            drop(hole_ref); // Drop the borrow

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
                // Create a let binding, so we can use it later
                let hole_ref = hole.value.borrow();

                match &*hole_ref {
                    Hole::Empty(lvl) if *lvl > ctx.level => {
                        // Drop the hole ref so we can get a new mutable reference
                        // for the hole
                        drop(hole_ref);

                        // Creates a new type variable
                        let new_type_var = ctx.new_fresh_variable();
                        quantifiers.push(new_type_var.clone());

                        // Updates the contents of the hole
                        // with the new type variable.
                        *hole.value.borrow_mut() = Hole::Filled(Type::Variable(new_type_var));
                    }
                    Hole::Filled(type_repr) => {
                        let mut type_repr = type_repr.clone();

                        // Drop the hole ref so we can get a new mutable reference
                        // for the hole
                        drop(hole_ref);

                        generalize_over(ctx, quantifiers, &mut type_repr);

                        // Updates the contents of the hole
                        // with the new type generalized.
                        *hole.value.borrow_mut() = Hole::Filled(type_repr);
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

    use crate::{
        type_error,
        typing::{Context, Hole, HoleRef, Level, Type},
    };

    /// Checks if a hole is valid for unification. We need to do the following checks:
    ///
    /// 1. Occurs check: If the variable not occurs in the type, infinite types are impossible.
    /// 2. Level check: If the level of the hole is greater than the level of the context, we can't unify it.
    fn pre_check_hole(
        ctx: &Context,
        hole: HoleRef,
        scope: Level,
        type_repr: Type,
    ) -> Result<(), crate::error::TypeError> {
        match type_repr {
            Type::Fun(_, _) => todo!(),
            Type::Forall(_, _) => todo!(),
            Type::Bound(_) => todo!(),
            Type::Hole(local_hole) if Rc::ptr_eq(&local_hole.value, &hole.value) => {
                return Err(type_error!("occurs check: infinite type"));
            }
            Type::Hole(local_hole) => {
                // Create a let binding, so we can use it later
                let new_hole = local_hole.value.clone();
                let hole_ref = new_hole.borrow();

                match &*hole_ref {
                    Hole::Empty(lvl) if *lvl > scope => {
                        // Drop the hole ref so we can get a new mutable reference
                        // for the hole
                        drop(hole_ref);

                        // Updates the contents of the hole
                        // with the new empty hole
                        *new_hole.borrow_mut() = Hole::Empty(scope);
                    }
                    Hole::Filled(type_repr) => pre_check_hole(ctx, hole, scope, type_repr.clone())?,
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
        pub fn fill(&self, ctx: &Context, sema: Type) -> Result<(), crate::error::TypeError> {
            let hole_ref = self.value.borrow();

            match &*hole_ref {
                Hole::Empty(scope) => {
                    // Deref the scope so we can use it later
                    let scope = *scope;

                    // Drop the hole ref so we can get a new mutable reference
                    // for the hole
                    drop(hole_ref);

                    // Checks the hole before filling it, so we can avoid
                    // mismatched levels and infinite types.
                    pre_check_hole(ctx, self.clone(), scope, sema.clone())?;

                    // Updates the contents of the hole
                    // with the new type
                    *self.value.borrow_mut() = Hole::Filled(sema);
                }
                Hole::Filled(type_repr) => {
                    unify(ctx, sema, type_repr.clone())?;
                }
            }

            Ok(())
        }
    }

    /// Unify two types. Perfmors equality checks and fills holes.
    ///
    /// It can return type errors.
    pub fn unify(ctx: &Context, sema_a: Type, sema_b: Type) -> Result<(), crate::error::TypeError> {
        match (sema_a, sema_b) {
            // Hole unification, attributing value
            // to the holes
            (Type::Hole(hole), sema) => hole.fill(ctx, sema)?,
            (sema, Type::Hole(hole)) => hole.fill(ctx, sema)?,

            // Constructor unification
            (Type::Variable(name_a), Type::Variable(name_b)) if name_a == name_b => {}
            (Type::Constr(name_a), Type::Constr(name_b)) if name_a == name_b => {}

            // Function unification
            (Type::Fun(domain_a, codomain_a), Type::Fun(domain_b, codomain_b)) => {
                unify(ctx, *domain_a, *domain_b)?;
                unify(ctx, *codomain_a, *codomain_b)?;
            }

            // Forall unification
            (Type::Forall(a, type_a), Type::Forall(b, type_b)) => {
                // Alpha equivalence betwhen quantifiers:
                // - `forall A. A -> A` is equivalent to `forall B. B -> B`
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
        pub fn unify(&self, sema_a: Type, sema_b: Type) -> Result<Type, crate::error::TypeError> {
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
    use crate::{
        typing::{Context, Hole, HoleRef, Type},
        unification::unify,
    };

    enum Direction {
        Left,
        Right,
    }

    /// Performs the subtyping relation between two types.
    ///
    ///
    /// # Parameters
    ///
    /// - `direction`: The direction of the subtyping relation. If it's checking or inferring
    /// the left or right side of the relation.
    fn sub_hole(
        ctx: &Context,
        hole: HoleRef,
        sema: Type,
        direction: Direction,
    ) -> Result<(), crate::error::TypeError> {
        let new_hole = hole.value.clone();
        let hole_ref = new_hole.borrow();

        match &*hole_ref {
            Hole::Empty(scope) => {
                // Deref the scope so we can use it later
                let scope = *scope;

                // Drop the hole ref so we can get a new mutable reference
                // for the hole
                drop(hole_ref);

                match (direction, sema) {
                    // Left rules
                    (Direction::Left, Type::Forall(name, type_repr)) => {
                        let type_repr = *type_repr.clone();
                        let ctx = ctx.clone().create_new_type(name.clone());

                        sub_hole(&ctx, hole, type_repr, Direction::Left)?;
                    }
                    (Direction::Left, Type::Fun(domain, codomain)) => {
                        let domain = *domain.clone();
                        let codomain = *codomain.clone();

                        let hole_a = HoleRef::new(Hole::Empty(scope));
                        let hole_b = HoleRef::new(Hole::Empty(scope));

                        *hole.value.borrow_mut() = Hole::Filled(Type::Fun(
                            /* domain   = */ Box::new(Type::Hole(hole_a.clone())),
                            /* codomain = */ Box::new(Type::Hole(hole_b.clone())),
                        ));

                        // Subtyping relation is contravariant on the domain
                        sub_hole(ctx, hole_a, domain, Direction::Right)?;
                        sub_hole(ctx, hole_b, codomain, Direction::Left)?;
                    }

                    // Right rules
                    (Direction::Right, Type::Forall(name, type_repr)) => {
                        let type_repr = *type_repr.clone();
                        let sema = ctx.instantiate(&name, type_repr);

                        sub_hole(&ctx, hole, sema, Direction::Right)?;
                    }
                    (Direction::Right, Type::Fun(domain, codomain)) => {
                        let domain = *domain.clone();
                        let codomain = *codomain.clone();

                        let hole_a = HoleRef::new(Hole::Empty(scope));
                        let hole_b = HoleRef::new(Hole::Empty(scope));

                        *hole.value.borrow_mut() = Hole::Filled(Type::Fun(
                            /* domain   = */ Box::new(Type::Hole(hole_a.clone())),
                            /* codomain = */ Box::new(Type::Hole(hole_b.clone())),
                        ));

                        // Subtyping relation is contravariant on the domain
                        sub_hole(ctx, hole_a, domain, Direction::Left)?;
                        sub_hole(ctx, hole_b, codomain, Direction::Right)?;
                    }

                    // For everything else, a <: b, only if a = b
                    (_, sema) => hole.fill(ctx, sema)?,
                }
            }

            // Tries to fill the hole with the type
            Hole::Filled(type_repr) => {
                sub(ctx, type_repr.clone(), sema)?;
            }
        };

        Ok(())
    }

    /// Performs the subtyping relation between two types.
    pub fn sub(ctx: &Context, sema_a: Type, sema_b: Type) -> Result<(), crate::error::TypeError> {
        match (sema_a, sema_b) {
            // Hole unification, attributing value
            (Type::Hole(hole), sema) => sub_hole(ctx, hole, sema, Direction::Left)?,
            (sema, Type::Hole(hole)) => sub_hole(ctx, hole, sema, Direction::Right)?,

            // Forall subsumtipon
            (sema_a, Type::Forall(name, type_repr)) => {
                let ctx = ctx.clone().create_new_type(name.clone());

                sub(&ctx, sema_a, *type_repr.clone())?;
            }
            (Type::Forall(name, type_repr), sema_b) => {
                let sema_a = ctx.instantiate(&name, *type_repr.clone());

                sub(&ctx, sema_a, sema_b)?;
            }

            // Function subsumption
            (Type::Fun(domain_a, codomain_a), Type::Fun(domain_b, codomain_b)) => {
                sub(ctx, *domain_b, *domain_a)?;
                sub(ctx, *codomain_a, *codomain_b)?;
            }

            // For everything else, a <: b, only if a = b
            (a, b) => unify(ctx, a, b)?,
        };

        Ok(())
    }

    impl Context {
        /// Performs the subtyping relation between two types.
        pub fn sub(&self, sema_a: Type, sema_b: Type) -> Result<Type, crate::error::TypeError> {
            let type_repr = sema_a.clone();
            sub(self, sema_a, sema_b)?;
            Ok(type_repr)
        }
    }
}

/// The mutually recursive type check functions of this simple programming language.
pub mod typer {
    use crate::{
        ast::Expr,
        type_error,
        typing::{Context, Hole, HoleRef, Type},
    };

    impl Context {
        /// Checks the type of an expression.
        pub fn check(&self, term: Expr, type_repr: Type) -> Result<(), crate::error::TypeError> {
            match (term, type_repr) {
                (term, ref type_repr @ Type::Hole(ref hole)) => {
                    let hole = hole.clone();
                    let hole_ref = hole.value.borrow();

                    match &*hole_ref {
                        Hole::Empty(_) => {
                            // Drop the hole ref so we can get a new mutable reference
                            // for the hole
                            drop(hole_ref);

                            let synth = self.infer(term)?;
                            self.sub(synth, type_repr.clone())?;
                        }
                        Hole::Filled(local) => {
                            // Clone the local type so we can use it later
                            let local = local.clone();

                            // Drop the hole ref so we can get a new mutable reference
                            // for the hole
                            drop(hole_ref);

                            self.sub(type_repr.clone(), local.clone())?;
                        }
                    }
                }
                (term, Type::Forall(name, type_repr)) => {
                    let bound = Type::Bound(self.level);
                    let ctx = self.clone().create_new_type(name.clone());

                    ctx.check(term, type_repr.clone().substitute(&name, bound))?;
                }
                (Expr::Abstr(domain_e, codomain_e), Type::Fun(domain_t, codomain_t)) => {
                    let domain_t = *domain_t.clone();
                    let ctx = self.clone().create_variable(domain_e.text, domain_t);

                    ctx.check(*codomain_e.clone(), *codomain_t.clone())?;
                }
                (Expr::Let(name, value, expr), type_repr) => {
                    let expr_type = self.infer(*value.clone())?;
                    let ctx = self.clone().create_variable(name.text, expr_type);

                    ctx.check(*expr.clone(), type_repr)?;
                }

                // Tries the default
                (term, type_repr) => {
                    let synth = self.infer(term)?;
                    self.sub(synth, type_repr)?;
                }
            }

            Ok(())
        }

        /// Synthesizes the type of an expression.
        pub fn infer(&self, term: Expr) -> Result<Type, crate::error::TypeError> {
            match term {
                Expr::Value(_) => Ok(Type::Constr("Int".into())),
                Expr::Ident(name) => self.lookup(&name.text).cloned(),
                Expr::Annot(expr, type_repr) => {
                    let type_repr = Type::from(*type_repr);
                    self.check(*expr, type_repr.clone())?;
                    Ok(type_repr)
                }
                Expr::Apply(f, arg) => {
                    let f_type = self.infer(*f)?;
                    self.apply(f_type, *arg)
                }
                Expr::Let(name, value, expr) => {
                    let expr_type = match &*value {
                        // If it's an abstraction, we should generalize it before
                        // checking the type of the expression
                        expr @ Expr::Abstr(_, _) => {
                            let type_rep = self.clone().create_new_type("_").infer(expr.clone())?;

                            self.generalize(type_rep)
                        }
                        _ => self.infer(*expr.clone())?,
                    };
                    let ctx = self.clone().create_variable(name.text, expr_type);

                    ctx.infer(*expr)
                }
                Expr::Abstr(name, expr) => {
                    let domain = Type::Hole(HoleRef::new(Hole::Empty(self.level)));
                    let ctx = self.clone().create_variable(name.text, domain.clone());
                    let codomain = ctx.infer(*expr)?;

                    Ok(Type::Fun(domain.into(), codomain.into()))
                }
            }
        }

        /// Applies the type of an expression to another expression.
        ///
        /// It has a weird symbol in "Complete and Easy"..
        pub fn apply(&self, f: Type, term: Expr) -> Result<Type, crate::error::TypeError> {
            match f {
                Type::Fun(domain, codomain) => {
                    self.check(term, *domain)?;

                    Ok(*codomain)
                }
                Type::Forall(name, type_repr) => {
                    self.apply(self.instantiate(&name, *type_repr), term)
                }
                Type::Hole(hole) => {
                    let hole = hole.clone();
                    let hole_ref = hole.value.borrow();

                    match &*hole_ref {
                        Hole::Empty(scope) => {
                            let hole_a = HoleRef::new(Hole::Empty(*scope));
                            let hole_b = HoleRef::new(Hole::Empty(*scope));

                            // Drop the hole ref so we can get a new mutable reference
                            // for the hole
                            drop(hole_ref);

                            *hole.value.borrow_mut() = Hole::Filled(Type::Fun(
                                /* domain   = */ Box::new(Type::Hole(hole_a.clone())),
                                /* codomain = */ Box::new(Type::Hole(hole_b.clone())),
                            ));

                            self.check(term, Type::Hole(hole_a))?;

                            Ok(Type::Hole(hole_b))
                        }
                        Hole::Filled(type_repr) => self.apply(type_repr.clone(), term),
                    }
                }
                _ => Err(type_error!(
                    "Expected a function type, found {:?}",
                    f.debug(self)
                )),
            }
        }
    }
}

fn main() {
    println!("Hello, world!");
}
