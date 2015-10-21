# Notes on a few of the chapters in the SF book

Lest I forget everything I learn from the SF book, I'll collect on this page
some concise notes about some of the most important concepts explained in the SF book.

(For now, we'll start from Chapter 6: MoreCoq, the last section of which
contains a nice summary of all the tactics learned in the first 6 chapters.)

## MoreCoq.v

### The **apply** tactic.
When the goal to be proved is exactly the same as some hypothesis `H`
in the context (or some previously proved lemma `L`), we can simply
apply `H` (or `L`).

Sometimes Coq needs some help figuring out how `H` or `L` can be applied
in the current context.  The **apply...with...** tactic can be helpful.

### The **inversion** tactic.
For all inductively defined types, all
constructors are injective, and the values built from distinct
constructors are never equal.  The **inversion** tactic can be used to
exploit these facts.

Suppose `H` is a hypothesis in the context of the form
`C a1 a2 ... an = D b1 b2 ... bm` for some constructors `C` and `D`
and arguments `a1 ... an` and `b1 ... bm`.
Then `inversion H` instructs Coq to "invert" this
equality to extract the information it contains about these terms:

- If `C` and `D` are the same constructor, then we know, by the
  injectivity of this constructor, that `a1 = b1`, `a2 = b2`,
  etc.; `inversion H` adds these facts to the context, and tries
  to use them to rewrite the goal.

- If `C` and `D` are different constructors, then the hypothesis
  `H` is contradictory.  That is, a false assumption has crept
  into the context, and this means that any goal whatsoever is
  provable!  In this case, `inversion H` marks the current goal as
  completed and pops it off the goal stack.


### Using tactics on hypotheses.
This is useful for applying forward and backward reasoning.
For example, suppose we have some
conditional statement `L` of the form `L1 -> L2`.
Then the tactic `apply L in H` matches some
 `H` against `L1` and, if successful, replaces it with `L2`.

In other words, `apply L in H` gives us a form of
**forward reasoning** -- from `L1 -> L2` and a hypothesis matching
`L1`, it gives us a hypothesis matching `L2`.

By contrast, `apply L` is **backward reasoning** -- it says that if
our current goal is to prove `L2`, and if we know
`L` (that is,  `L1 -> L2`), then it suffices to prove `L1`.

**Example:** Suppose the current context looks like this

    H1 : P -> Q
	H2 : P
	============

Then you could do `apply H1 in H2`.  (This may seem a little
counterintuitive at first, and maybe `apply H2 in H1` seems more
natural here.)  The result is

    H1 : P -> Q
	H2 : Q
	============

That is, the hypothesis that you apply (`H2`) is the one that gets
replaced (by the consequent of the implication to which `H2` was applied).


### Using **destruct** on Compound Expressions

In general, the `destruct` tactic can be used to perform case
analysis of the results of arbitrary computations.  If `e` is an
expression whose type is some inductively defined type `T`, then,
for each constructor `c` of `T`, `destruct e` generates a subgoal
in which all occurrences of `e` (in the goal and in the context)
are replaced by `c`.

Sometimes, doing a `destruct` on a compound expression (a
non-variable) `e` will erase information we need to complete a proof.
Instead, we want to substitute away all existing occurences of `e`,
but at the same time add an equation to the context that records
which case we are in.  The `eqn:` qualifier allows this.

For example,

    destruct e eqn:Heq.

will add to the context an hypothesis called `Heq` which manifests
the form (or value) `e` takes during the current branch of the
destruction.



### Review

Here's a list of all the tactics covered in the first 6 chapters of the SF book.

- `intros`: move hypotheses/variables from goal to context.

- `reflexivity`: finish the proof (when the goal looks like `e = e`).

- `apply`: prove goal using a hypothesis, lemma, or constructor.

- `apply... in H`: apply a hypothesis, lemma, or constructor to a hypothesis in
  the context (forward reasoning).

- `apply... with...`: explicitly specify values for variables that cannot be
  determined by pattern matching.

- `simpl`: simplify computations in the goal.

- `simpl in H`: ... or a hypothesis.

- `rewrite`: use an equality hypothesis (or lemma) to rewrite the goal.

- `rewrite ... in H`: ... or a hypothesis.

- `symmetry`: changes a goal of the form `t=u` into `u=t`.

- `symmetry in H`: changes a hypothesis of the form `t=u` into `u=t`.

- `unfold`: replace a defined constant by its right-hand side in the goal.

- `unfold... in H`: ... or a hypothesis.

- `destruct... as...`: case analysis on values of inductively defined types.

- `destruct... eqn:...`: specify the name of an equation to be added to the
  context, recording the result of the case analysis.
  
- `induction... as...`: induction on values of inductively defined types.

- `inversion`: reason by injectivity and distinctness of constructors.

- `assert (e) as H`: introduce a "local lemma" `e` and call it `H`.

- `generalize dependent x`: move the variable `x` (and anything else that
  depends on it) from the context back to an explicit hypothesis in the goal
  formula.

## Logic


