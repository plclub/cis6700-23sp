# Advanced Topics in Programming Languages
# CIS 6700, Spring 2023


        Instructor:     Stephanie Weirich
        Time:           MW 3:30-5PM
        Location:       Towne 303
        Prerequisite:   CIS 5000 or PhD student status

The [course syllabus](https://docs.google.com/spreadsheets/d/1i6NLEXnoAy6wkygLAEubdfVrhkF-se07Q6fwoAeTbK4/edit#gid=0) lists
the overall plan of the semester.

## Introduction and course goals

My goal for this course is to extend and deepen your knowledge of programming
language theory. This means that we'll start with some classic results, but
look at them through the lens of modern tools, such as proof assistants. We'll
also read and discuss many classic and recent research papers that relate to
the course topics.

In taking this course, you should gain a firm foundation for the sorts of
proofs that appear in PL research papers, such as in POPL and ICFP, as well as
the ability to experiment with new ideas using a proof assistant.

## Target audience 

The target audience for this course is a PhD student. Other students with an
interest in programming language research are welcome, but CIS 5000 is a
prerequisite.  More generally, we expect that you have some experience with
functional programming (Haskell or OCaml), have seen a type safety proof for
the simply-typed lambda calculus (e.g. in CIS 5000). You'll also want to have
experience using the Coq proof assistant.

## Course format and expectations

This is a seminar course, so I expect everyone to work with me to help make this 
course successful. Some participants will be taking this course for a grade, to 
satisfy a course requirement for their PhD program. Others, who are generally 
interested in programming language theory are welcome to attend any class without 
registering.

+ If you are taking this class for a grade, please
  - Come to every class prepared (I'll announce the reading for the next class
  ahead of time)
  - Send me 1-2 questions the morning before each class (via email: sweirich@seas.upenn.edu)
  - Prepare and give one lecture during the semester 
  - Try to fill in the holes in the mechanized proofs at the beginning of the 
    semester to make sure you are up to speed
  - Complete a semester project (alone or in small  groups) to go deeper on a particular topic.
   * replicate the proofs in a classic paper 
   * extend a classic paper with a new feature
   * some other exploration

+ If you are auditing this semester, please
   - Come to every class prepared (I'll announce the reading for the next class
     ahead of time)
   - Send me 1-2 questions before each class (via email: sweirich@seas.upenn.edu)
  
## Course communication

I've created a slack channel #cis6700 in the [plclub
slack](plclub.slack.com). If you do not have access to this slack, please let
me know. You should join this channel to receive announcements about the
course.

Course notes and other information will be distributed via [github](https://github.com/plclub/cis6700-23sp).
  
## Mask policy

Masks are optional, but I strongly encourage you to wear one, especially during the first few 
weeks of the semester.
  
## Topics

The [course syllabus](https://docs.google.com/spreadsheets/d/1i6NLEXnoAy6wkygLAEubdfVrhkF-se07Q6fwoAeTbK4/edit#gid=0) lists
the overall plan of the semester.

This syllabus is divided into four parts:

1. Untyped lambda calculus 
2. Simply-typed lambda calculus 
3. Parametric Polymorphism 
4. Effects and Co-effects in types

### The Untyped Lambda Calculus

History: this system was developed by Alonzo Church in 1930s as a foundation
for logic.

This system can encode arbitrary, nonterminating computation (i.e. Turing
machines). We'll look at these encodings and how they work.

However, one may still define a consistent equational theory about
lambda-calculus terms. In this case, consistency means that the theory is
nontrivial: i.e. there are (at least) two lambda calculus terms that cannot be
shown equal by the theory. The proof of consistency of the equational theory
is the Church-Rosser Theorem.

### Stlc

History: developed by Church in 1940 as a consistent restriction of the lambda
calculus.

An important property of the simply-typed lambda calculus (Stlc) cannot encode
all computation. If we want features such as products, sums, and other forms
of data, we need to extend the language.

The key classical result about Stlc is *strong normalization*: all
reductions sequences are finite. A corollary of this result is that the
equational logic of Stlc is decidable. We can tell whether two terms are equal
by comparing their normal forms.

We'll look at two proofs related to this result. As a warm-up, we'll start with a 
proof that all Stlc programs terminate. This proof, due to Tait, is based on defining 
a logical relation.

Second, we will look at a type-directed normalization strategy called
"normalization-by-evaluation" that can be used to decide the equivalence of
Stlc terms, and its proof of correctness.

### Polymorphic Lambda Calculus / System F

History: independently developed by Reynolds (1974) and Girard (1971).

This system describes parametric polymorphism in programming languages. It can
express some Church-style lambda calculus encodings, but not arbitrary
recursion.

Like Stlc, this system is strongly normalizing. A generalization of the
logical relation termination proof gives us the *parametricity* theorem: the
fact that the type alone of a term can tells us something about
it. Parametricity also means that types are irrelevant to computation: we can
erase all type arguments and still run the code.

Parametric polymorphism has been the foundation of modern functional
programming languages such as ML and Haskell since the development of the
Hindley-Milner type system. Essentially, this type system is a restriction of
the polymorphic lambda calculus that supports complete type inference. We'll
look at the design and implementation of this type system along with modern
extensions.

### Effects / Co-effects 

The last topic will be a closer look at effects and co-effects in typed lambda
calculi.  First, we'll start with call-by-push-value, a version of the lambda
calculus that distinguishes values and computations. Then, we'll look at how
type systems can track computational effects, starting with the FX programming
language from the 1980s. We'll then jump to more modern treatments of
Co-effects, via the Granule language and Linear Haskell. Finally, we'll see
how these both relate to modal type systems.

## Mechanized proofs

The first part of the semester will also focus on mechanically checked
versions of classic proofs using both the Coq and Agda proof assistants.  As
the semester progresses, we'll shift to more recent results and discuss proofs
more informally.

In Coq, we'll go over modeling lambda-calculus term using a locally nameless
representation in Coq, as supported by the tools Ott and LNgen. After that,
we'll switch to Agda and look at a well-scoped and well-typed de Bruijn
representations.

## Resources

- [Coq Proof Assistant](https://coq.inria.fr/)				
- [Software Foundations](https://www.cis.upenn.edu/~bcpierce/sf/)
- [Ott: Tool for the working semanticist](http://www.cl.cam.ac.uk/~pes20/ott/)
- [MetaLib](https://github.com/plclub/metalib)		
- [LNgen](https://github.com/plclub/lngen)		
- [Practical Foundations for Programming Languages](http://www.cs.cmu.edu/~rwh/pfpl.html)
- [Programming Language Foundations in Agda](https://plfa.github.io/)
