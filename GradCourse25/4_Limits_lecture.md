# Filters

## Definition

A filter `F` on a type `α` is set in `Set α` (*i. e.* a collection of sets in `α`) such that:
1. The largest set `⊤ = Set.univ` is in `F`;
2. If `s,t : Set α` and `s ⊆ t`, then `s ∈ F` implies that `t ∈ F` (they are "upwards closed")
3. `F` is stable by finite intersections.

More precisely, `Filter` is a structure:

```lean
structure Filter (α : Type*) : Type*
  | sets : Set (Set α)
  | univ_sets : univ ∈ self.sets
  | sets_of_superset : ∀ {x y : Set α}, x ∈ self.sets → x ⊆ y → y ∈ self.sets
  | inter_sets : ∀ {x y : Set α}, x ∈ self.sets → y ∈ self.sets → x ∩ y ∈ self.sets
```

* If `F` is a filter on `α`, and `U` is a subset of `α` then we can
write `U ∈ F` as on paper, instead of the pedantic `U ∈ F.sets`.

+++ Some examples of filters
* Given a term `a : α`, the collection of all sets containing `a` is the **principal** filter (at `a`): this generalises to any set `S ⊆ α`, being the case `S = {a}`. It is denoted `𝓟 S`, typed `\MCP S`.

`⌘`

* The collection of all sets of natural integers (or real numbers, or rational numbers...) that are
  "large enough" or "small enough" are filters. They are called `atTop` and `atBot`, respectively.

* More generally—and this is really the key case connecting these notions with some topology—in a topological space `X`, the collection of all neighbourhoods (or of all open neighbourhoods) of a subspace is a filter. We content ourselves with the case of metric spaces (and of `ℝ`, quite often).

`⌘`
+++

## Why filters
**RISCRIVERE DA QUI....**

Filters are (among other things) a very convenient way
to talk about convergence. 

For example, consider a function `f : ℝ → ℝ` and `a,b : ℝ`.

Suppose that we want to say that the limit of `f` at `a`
is `b`. This means that, for every `ε > 0`, there exists
`δ > 0` such that `f` sends `(a - δ, a + δ)` to
`(b - ε, b + ε)`.
We can reformulate this by saying that `f ⁻¹' (b - ε, b + ε)`
is in the filter of neighborhoods of `a` for every `ε`, which
means: `∀ (U : nhds b), f ⁻¹' U ∈ nhds a`.

But now suppose to say that `f(x)` tends to `b` as `x` tends to
`a` on the left. This means that for every `ε > 0`, there exists
`δ > 0` such that `f` sends `(a - δ, a]` to `(b - ε, b + ε)`.
With filters, this becomes: `∀ (U : nhds b), f ⁻¹'U ∈ nhds_left a`.

We can similarly express things like "`f(x)` approaches `b`
on the right when `x` approaches `a` on the left", etc.

Now suppose that we want to say `f(x)` tends to `b` as `x`
tends to `+ ∞`. This means that, for every `ε > 0`, there
exists `M : ℝ` such that `f` sends `[M, + ∞)` to
`(b - ε, b + ε)`. Or, with filters:
`∀ (U : nhds b), f ⁻¹' U ∈ Filter.atTop`.
We could similarly express the fact that `f(x)` approaches
`b` from the left as `x` tends to `+ ∞`, by using `nhds_left b`
instead of `nhds`.
`∀ (U : nhds_left b), f ⁻¹' U ∈ Filter.atTop`.


Similarly, if `u : ℕ → ℝ` is a sequence (here with real values,
but it could have values in any topological space), we can
express the fact that `u` converges to `b : ℝ` with filters:
`∀ (U : nhds b), f ⁻¹' U ∈ Filter.atTop`. --i.e. f ⁻¹' U contains
-- an interval [n, +∞).

Note that all these definitions of convergence can be written
in exactly the same way once we decide to use filters. This is
already nice, but it starts being really powerful when we
want to prove theorems about limits.

For example, let `f,g : ℝ → ℝ` and let `a,b,c : ℝ`. We can
prove that, if `f(x)` tends to `b` as `x` tends to `a`
and `g(y)` tends to `c` as `y` tends to `b`, then `(g ∘ f) (x)`
tends to `c` as `x` tends to `a`.
But then suppose that we want to use that, if `f(x)` tends to
`b` on the right as `x` tends to `a` on the left and `g(y)`
tends to `c` on the left as `y` tends to `b` on the right, then
`(g ∘ f) (x)` tends to `c` on the left as `x` tends to `a` on
the left. On paper, we can just say that "the proof is similar",
but Lean won't accept that, so we would have to rewrite the
proof. Now think about all the different possibilities
(including limits at infinity, limits as `x` is only in a certain
subset etc), and ask yourselves if you really want to write the
resulting 3487 lemmas (conservative estimation).

If instead we can express everything with filters, then
we only need to prove each statement once.
**... A QUI**

+++ Convergence, Take 1
First attempt to define convergence: `f : X → Y` is a
function, we have a filter `F` on `X`, a filter `G` on
`Y`, and we want to say `f` tends to `Y` along `X`.
We generalize the definition that appeared before, **E ARRIVARE A `Filter_backwards`**

A small drawback of this definition is that it exposes a quantifier, and this is 
1. Aesthetically unpleasant
1. Slightly cumbersome from the formalisation point of view, since it forces us to constantly use `intro` and to reason "with terms" rather than trying to have a more abstract approach directly working with their types.
+++

+++ Convergence, Take 2
An intuitive way to think about filters, and a reformulation
of convergence.

Remember that, for every `s : Set α`, we have the principal filter
generated by `s`: it is the filter whose elements are sets
containing `s`.

We think of this filter as standing in for `s`, and we think of
more general filters as "generalized sets" of `α`. With this
point of view, if `F` is a filter on `α` and `s : Set α`, saying
that `s ∈ F` means that `s` "contains" the corresponding
"generalized set".

For example, if `α` is `ℝ` (or more generally if `α` has a
topology) and `a : α`, then `𝓝 a` is "the set of elements
close enough to `a`".
If `α` has a (pre)order, then `Filter.atTop` is "the set
of elements that are big enough".

Now that we think of filters as generalized sets,
let's extend some set notions to them.

1. The first is the order relation: sets on `α` are
ordered by inclusion. How does it translate to filters?
Well, it means that every set that contains `t` also
contains `s`:
1. The second notion is the image of a filter by
a function `f : α → β`. This operation is called
`Filter.map`. The idea is that, if `F : Filter α`
and `V : Set β`, the statement
`V ∈ Filter.map f F ↔ f ⁻¹' V ∈ F` should be true
by definition.

We can now reformulate the notation of convergence
using these notions. The idea is that, for example,
if `f : ℝ → ℝ`, then `f` tends to `b : ℝ` at `a : ℝ`
if, for every `x : ℝ` close enough to `a`, its image
`f(x)` is close enough to `b`. In other words, `f` sends
the "set of elements close enough to `a`" to a "subset"
of "the set of elements close enough to `b`".


+++