# Groups (and Monoids)

The prototypical monoid is `ℕ`: it has an operation, a `0`, but no inverse.

In principle, we do not like monoids too much: they are somewhat weak algebraic structures. They are nonetheless crucial for our formalization of algebraic structures for (at least) two reasons

1. Groups are a generalization of monoids: if we can prove some properties only relying on the theory of monoids, it makes less lines to code.
1. Rings are endowed with *two* operations but are a group only for one of them; for the other they (typically) are a monoid

## Monoids

To say that a monoid...


`⌘`

## Groups

A group is a monoid `G` with inverses:

    inv : G → G
    inv_mul_cancel (g : G) : g⁻¹ * g = 1

Of course, there are also the notion of `AddGroup` with

    neg : A → A
    neg_add_cancel (a : A) : -a + a = 0

and notions 

* There is a `group` tactic that proves identities that holds in any group (equivalently, it proves those identities that hold in free groups). The equivalent version for *commutative* groups is `abel`. 

Concerning group homomorphisms, they are just **monoid** homomorphisms, so they are a structure with simply three structures: the function itself, and two proofs that it preserves multiplication and sends `1` to `1`.

`⌘`

Of course, there is also the notion a group *isomorphism*: this is a structure with four fields

    structure GroupEquiv (G H : Type*) [Group G] [Group H] where
    | toFun : G →* H
    | invFun : H →* G
    | left_inv : invFun ∘ toFun = id
    | right_inv : toFun ∘ invFun = id

+++ How do you *state* that something is a group isomorphism?
* To *state* something means creating a type in `Prop`
* To prove a statement means creating an *inhabited* type in `Prop`
* A `GroupEquiv` is not a type in `Prop`, it can have way too many terms...

    def IsoOfBijective (G H : Type*) [Group G] [Group H] (f : G →* H)
        (h_surj : Surjective f) (h_inj f) : G ≃* H := by

+++

`⌘`

## Subgroups
A subgroup is *not defined* as a group that is also a subset. It is a subset closed under multiplication:

    structure Subgroup (G : Type*) [Group G] where
    | carrier : Set G
    | mul_mem (x y : G) : x ∈ carrier → y ∈ carrier → x * y ∈ carrier
    | inv_mem (x : G) : x ∈ carrier → x⁻¹ ∈ carrier

* This creates a new type `Subgroup G` whose terms are **the subgroups of G**. As for group isomorphisms above, this is not the proposition "`H` is a subgroup". You should expect to encounter expressions like

    H : Subgroup G

to declare that `H` is a subgroup of `G` (technically: a term of the type parametrising such subgroup structures).

* How can we prove that something *is* a subgroup? Again, by *defining* a term!

+++ Trivial ones?
Among all subgroups of a group `G`, two fundamental examples are the trivial group `{1} ⊆ G` and the whole group `G ⊆ G`. To treat these things, we borrow the language of orders.

Indeed, subgroups are *ordered* (by inclusion of their carrier), so `{1} = ⊥` (the bottom element, typed `\bot` and `G = ⊤`, the top element (typed with `\top`).


+++

# Rings