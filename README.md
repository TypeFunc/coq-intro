# Coq Resources

## Getting Started

This repository is mainly intended for my research students who are interested
in learning about the Coq proof assistant. 

+ **What is Coq?**
  Coq is a proof assistant and a functional programming language.

+ **What is a proof assistant?**
  A proof assistant is a tool that automates the more routine aspects of building
  proofs while depending on human guidance for more difficult aspects.
  Coq is one such tool. It provides a rich environment for interactive
  development of machine-checked formal reasoning.  

### Installation 

There are a number of ways to get started with Coq, so I'll just describe my experience.
  
Installation of Coq can be very hard or very easy.  The first time I installed Coq, on
Ubuntu Linux, it was extremely easy.  But then I tried to get fancy and use a
more recent version of Coq than the one that comes stock with Ubuntu.  This
was a mistake.  It took many hours to get it configured, and I was worse off in
the end because some of my existing Coq programs would no longer run. 
(Coq 8.5 is not backward compatible with Coq 8.4.)  I had my reasons for
wanting to use a more recent version of Coq, but if you don't, then I
recommend opting for whatever is the simplest installation method available 
for your OS.

Here are some links that explain various ways to get Coq installed.
  
1. [The Official Coq website](https://coq.inria.fr/). You should probably
   start here; in particular, various versions of Coq can be downloaded from
   [this page](https://coq.inria.fr/download).

2. **Unofficial installation instructions**
   Installation instructions come with the source or binaries that you
   download from the official Coq website, but sometimes that's not
   enough. Here are some unofficial resources that can help you get Coq
   installed the way you want it.
   - [Installing with apt-get on Linux](https://coq.inria.fr/cocorico/Installation%20of%20Coq%20on%20Linux)
   - [Installing with opam on Linux](http://coq-blog.clarus.me/use-opam-for-coq.html)
   - [Installing ver 8.5beta2+ssreflect on various platforms](http://ilyasergey.net/pnp/setup.html)

3. [ProofGeneral](http://proofgeneral.inf.ed.ac.uk/) is what you need if you
   want to use Emacs to interface with Coq. (If you decide to use the CoqIDE, you
   don't need ProofGeneral.)
   - [Development Release of ProofGeneral](http://proofgeneral.inf.ed.ac.uk/devel)
   - [ProofGeneral Manual for version 4.3pre](http://proofgeneral.inf.ed.ac.uk/htmlshow.php?title=Proof_General+manual&file=releases%2FProofGeneral-latest%2Fdoc%2FProofGeneral%2FProofGeneral.html#Top)
   - [ProofGeneral notes on using a Coq project file](http://proofgeneral.inf.ed.ac.uk/htmlshow.php?title=Proof_General+manual&file=releases%2FProofGeneral-latest%2Fdoc%2FProofGeneral%2FProofGeneral_12.html#Using-the-Coq-project-file)
  
  
### Trying it out

[Andrej Bauer's series of YouTube tutorials](http://www.youtube.com/watch?v=COe0VTNF2EA&list=PLDD40A96C2ED54E99&feature=share).
These videos are probably the fasted way to see exactly how one interacts with
Coq in the first place. For example, in the video
[How to use Coq with Proof General](http://youtu.be/l6zqLJQCnzo),
Andrej shows how to use Coq to prove
that Pierce's law is equivalent to the Law of Excluded Middle.  

(Proof General is one way to interact with Coq, which is the great for
those accustomed to the Emacs editor. For those who aren't into Emacs,
an alternative interface to Coq exists, called CoqIDE, about which I know
absolutely nothing. I installed Coq and Proof General on Ubuntu 14.04 very
easily using the Synaptic package manager; no custom configuration required.)

### Going further

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

Find the latest version of the Software Foundations book at the official website:

[http://www.cis.upenn.edu/~bcpierce/sf/current/index.html](http://www.cis.upenn.edu/~bcpierce/sf/current/index.html)

**WARNING** If you installed the most recent version of Coq, it's possible 
some of the code in the SF book will not work.  There are a few solutions to 
this problem:
1. downgrade your version of Coq to one that is compatible with SF. As of this 
   writing, all the SF code works fine on version 8.4, but some is incompatible 
   with version 8.5.
2. replace some or all of the SF files with modified versions that some others 
   have made available. One example is here.
3. As you work through the SF book, modify the parts that don't work with your 
   version of Coq and get them to work.  There are some hints about how to do that 
   at 


### Going even further

One of our goals is to implement some mathematics in Coq, both to help us
better understand what we are doing and to (hopefully) help us push it further.

After learning the basics of Coq, members of the group may wish to try codifying
some general algebraic structures as *dependent types* or *records* in Coq.
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
   by Venanzio Capretta. This is older stuff, but it's legit and well written.
   It is summarized in 
   [Capretta's conference paper](http://www.duplavis.com/venanzio/publications/Universal_Algebra_TPHOLs_1999.pdf)
   and explained in great detail in
   [his phd thesis](http://www.cs.nott.ac.uk/~vxc/publications/Abstraction_Computation.pdf).
   Lots more info is available on [his homepage](http://www.duplavis.com/venanzio/).

3. [UniMath](https://github.com/UniMath/UniMath) is a Coq library aiming to formalize mathematics using the 
   univalent (HoTT) point of view.


### distributing your masterpiece

Once you have created something worthy of your immense talent, you might read
[this tutorial](http://coq-blog.clarus.me/make-a-coq-package.html) that explains how to
roll your own Coq package and distribute it to the world via opam. Of course, you could simply 
distribute it on your own website or github, but making an opam package gives your code
a bit of street cred, and makes it instantly usable by folks using opam.

