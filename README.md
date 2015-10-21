## Coq Resources

This repository is mainly intended for my research students who are interested
in learning about the Coq proof assistant. 

+ **What is Coq?**
  Coq is a proof assistant and a functional programming language.

+ **What is a proof assistant?**
  A proof assistant is a tool that automates the more routine aspects of building
  proofs while depending on human guidance for more difficult aspects.
  Coq is one such tool. It provides a rich environment for interactive
  development of machine-checked formal reasoning.  

+ **How to get started?**
  There are a number of ways to get started with Coq, so I'll just describe my
  experience.

  I first started by watching
  [Andrej Bauer's series of YouTube tutorials](http://www.youtube.com/watch?v=COe0VTNF2EA&list=PLDD40A96C2ED54E99&feature=share).
  These videos are probably the fasted way to see exactly how one interacts with
  Coq in the first place. For example, in the video
  [How to use Coq with Proof General][], Andrej shows how to use Coq to prove
  that Pierce's law is equivalent to the Law of Excluded Middle.  

  (Proof General is one way to interact with Coq, which is the great for
  those accustomed to the Emacs editor. For those who aren't into Emacs,
  an alternative interface to Coq exists, called CoqIDE, about which I know
  absolutely nothing. I installed Coq and Proof General on Ubuntu 14.04 very
  easily using the Synaptic package manager; no custom configuration required.)

+ **How to continue?**
  To go further and learn more about how to exploit Coq for theorem proving and
  functional programming, I highly recommend reading (and solving the
  exercises in) the first 5 or 6 chapters of the book, "Software Foundations."

  This SF book is an outstanding resource.  Not only is it well written and
  accessible, even to non-computer scientists, but also it's fun to read because
  of the many engaging exercises sprinkled through the book that test your
  understanding of the material.

  With some prior programming experience---and especially with some functional
  programming experience---you can probably proceed quickly through SF and learn
  a lot about Coq by solving most, if not all, of the exercises. I would guess
  that an intelligent undergraduate, with a little background in elementary 
  logic, math, and programming, could get through a few chapters of SF per week.

The file sf.tar.gz is the official (as of Feb 18, 2015) version of the book
Software Foundations.  Find the latest version at the official website for the
book:

[http://www.cis.upenn.edu/~bcpierce/sf/current/index.html](http://www.cis.upenn.edu/~bcpierce/sf/current/index.html)

The directory sf-solutions contains a version of the sf book with some of the
exercises filled in (only up to Chapter 4 or 5, so far).


[How to use Coq with Proof General]: http://youtu.be/l6zqLJQCnzo

# Summer 2015

This is the (README.md file of the) summer-2015 subdirectory of the
TypeFunc/Coq.git repsitory. Its purpose is to organize and keep a
record of some of our work during the summer months of 2015.

---------------------------------
## Preliminary Plans
+ cover the first 12 Chapters of the Software Foundations book,
  as well as some of the chapters on the lambda calculus.  
+ Work through the first 7 Chapters of "the pnp course."

### Software Foundations
This book is great!  I recommend that everyone in our group become familiar with
at least the first 12 chapters book, and then look at the chapters on the
lambda calculus.  (A schedule that will take us through the whole book in 8
weeks appears below.)

### The pnp course

[IMDEA: Programs and Proofs: Mechanizing Mathematics with Dependent Types](http://ilyasergey.net/pnp-2014/)
was a week-long summer school in August 2014, attended by a handful of students, and taught by Ilya Sergey.
I'll refer to this as "the pnp course."  It's significant for our group derives from
the fact that it is the only resource I have found that teaches Coq with a focus
on the mathematics instead of on principles of programming languages. 

The SSReflect library is used heavily in the pnp course.  It was developed to prove
the [Feit-Thompson odd order theorem](http://coqfinitgroup.gforge.inria.fr/).
The [SSReflect manual](http://ilyasergey.net/util/ssreflect-manual.pdf) is
freely available and not too big, so there's a copy in this repository (presently
in the courses/pnp directory).


--------------------------------------------------

## Schedule for 8-week Coq summer camp

The schedule below takes us through the Coq book in 8 weeks.

## Week 1

###  6/28
1.Basics: Functional Programming in Coq  
2.Induction: Proof by Induction  
3.Lists: Working with Structured Data  

### 06/30
**HW1 Due:** Basics.v, Induction.v, Lists.v

------------------------------

## Week 2

### 07/01
4.Poly: Polymorphism and Higher-Order Functions  
5.MoreCoq: More About Coq's Tactics  

### 07/03 Logic in Coq
6.Logic: Logic in Coq  

### 07/05
**HW 2 Due:** Poly.v, MoreCoq.v, Logic.v

------------------------------

## Week 3

### 07/08
7.Prop: Propositions and Evidence  
8.MoreLogic: More on Logic in Coq

### 07/10
9.ProofObjects: Working with Explicit Evidence in Coq


### 07/12
**HW 3 Due:** Prop.v, MoreLogic.v, ProofObjects.v

------------------------------

## Week 4

### 07/15
10.MoreInd: More on Induction  
11.SfLib: Software Foundations Library

### 07/17
12.Rel: Properties of Relations

### 07/19
**HW 4 Due:** MoreInd.v, SfLib.v, Rel.v

------------------------------

## Week 5

### 07/22
13.Imp: Simple Imperative Programs  
14.ImpParser: Lexing and Parsing in Coq

### 07/24
15.ImpCEvalFun: Evaluation Function for Imp  
16.(Extraction: Extracting ML from Coq) (probably skip)

### 07/26
**HW 5 Due:** Imp.v, ImpParser.v, ImpCEvalFun.v

---------------------------------

## Week 6

### 07/29
17.Equiv: Program Equivalence  
18.Hoare: Hoare Logic, Part I

### 07/31
19.Hoare: Hoare Logic, Part II  
20.HoareAsLogic: Hoare Logic as a Logic

### 08/02
**HW 6 Due:** Equiv.v, Hoare.v, Hoare2.v

---------------------------------------

## Week 7

### 08/05 
21.Smallstep: Small-step Operational Semantics  
22.Auto: More Automation

### 08/07
23.Types: Type Systems

### 08/09
**HW7 Due:** Smallstep.v, Auto.v, Types.v

------------------------------------------------

## Week 8

### 08/12 
24.Stlc: The Simply Typed Lambda-Calculus (STLC)  
25.StlcProp: Properties of STLC

### 08/14
26.MoreStlc: Soundness of the STLC  
27.Sub: Subtyping

### 08/16
**HW 8 Due:** Stlc.v, StlcProp.v, MoreStlc.v  
**Final Exam**

