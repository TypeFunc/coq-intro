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

### Codifying Mathematics

One of our goals is to implement some mathematics in Coq, both to help us
better understand what we are doing and to (hopefully) help us push it further.

After learning the basics of Coq, members of the group may wish to try codifying
some general algebraic structures as **dependent types** or **records** in Coq.
Fortunately, we don't have to start from scratch as there are already a number
of projects that attempt to do this.  We can study those efforts and learn from
what they have done and possibly make use of some of their libraries.

Here are links to a couple of projects that look promising for our purposes and
are probably good places to start:

1. [Math Classes](https://coq.inria.fr/cocorico/MathClasses)
   ([github repo](https://github.com/math-classes/math-classes),
   [coq doc](http://www.lix.polytechnique.fr/coq/pylons/coq/pylons/contribs/view/MathClasses/v8.4), 
   [more info](http://www.eelis.net/research/math-classes/)) by Spitters and van
   der Weegen, Radboud University, NL.

2. [Universal Algebra in Coq](http://www-sop.inria.fr/lemme/Venanzio.Capretta/universal_algebra.html)
   by Venanzio Capretta. This is older stuff, but it's legit, looks
   interesting and probably useful.
   It is summarized in 
   [Capretta's conference paper](http://www.duplavis.com/venanzio/publications/Universal_Algebra_TPHOLs_1999.pdf)
   and explained in great detail in
   [his phd thesis](http://www.cs.nott.ac.uk/~vxc/publications/Abstraction_Computation.pdf).
   Lots more info is available on [his homepage](http://www.duplavis.com/venanzio/).


