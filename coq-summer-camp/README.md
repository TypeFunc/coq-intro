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

