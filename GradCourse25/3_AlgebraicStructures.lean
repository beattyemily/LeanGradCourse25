import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Group

open Function Set

section Monoids


-- In this example, both `1` and `*` are understood automatically
-- **ToDo**
example (M : Type*) [Monoid M] (m : M) : m = m * 1 := by
  sorry

-- **ToDo**
-- @[to_additive]
lemma EqIfMulEq {M : Type*} [Monoid M] {a b c : M} (hba : b * a = 1) (hac : a * c = 1) :
    b = c := by
  sorry

example : Monoid Bool := sorry


-- `⌘`


-- **ToDo**
#synth Monoid Bool
#synth Monoid ℤ
#synth AddMonoid ℤ


-- `⌘`

-- **ToDo**
-- example (M : Type*) [AddMonoid M] (a b c : M) (hba : b * a = 1) (hac : a * c = 1) : b = c := by
example (M : Type*) [AddMonoid M] (a b c : M) (hba : b + a = 0) (hac : a + c = 0) : b = c := by
  sorry

-- **ToDo**
-- In general, `*`  and `+` are completely unrelated:
example (M : Type*) [Monoid M] [AddMonoid M] (a : M) : a * 1 = a + 0 := by
  sorry

-- yet...
-- **ToDo**
example (M : Type*) [Monoid M] [AddMonoid M] (a : M) : a * 0 = 0 := by
  sorry

-- **ToDo**
-- Too many structures at once!
example (M: Type*) [Monoid M] [CommMonoid M] (m₁ m₂ m₃ : M) : m₁ * m₂ * m₃ = m₂ * (m₁ * m₃) := by
  sorry


-- `⌘`

-- **Exercise**
-- Observe how Lean understands automatically where `1` and `*` live
example (M N : Type*) [Monoid M] [Monoid N] (f : M →* N) : f 1 = 1 := by
  sorry



-- **Exercise**
example (M N : Type*) [Monoid M] [CommMonoid N] (f : M →* N) (m₁ m₂ : M) (n : N) (h : f m₁ * n = 1) :
    f (m₁ * m₂) * n = f m₂ := by
  sorry

-- **Exercise**
example (M N : Type*) [CommMonoid M] [CommMonoid N] : CommMonoid (M →* N) := sorry


end Monoids

section Groups

-- **ToDo**
example {G : Type*} [Group G] (x y z : G) : x * (y * z) * (x * z)⁻¹ * (x * y * x⁻¹)⁻¹ = 1 := by
  sorry

-- **ToDo**
example {A : Type*} [AddCommGroup A] (a b : A) : a + 0 + b + 0 = b + a := by
  sorry

-- **ToDo**
example (G H : Type*) [Group G] [Group H] (f : G →* H) (g : G) : f (g⁻¹) = (f g)⁻¹ := by
  sorry


-- `⌘`


variable {G H : Type*} [Group G] [Group H]

-- **ToDo**
noncomputable --what's this?
def IsoOfBijective (G H : Type*) [Group G] [Group H] (f : G →* H)
    (h_surj : Surjective f) (h_inj : Injective f) : G ≃* H := by
  sorry

-- **ToDo**
example {G H : Type*} [Group G] [Group H] (f : G → H) (h : ∀ x y, f (x * y) = f x * f y) :
    G →* H := sorry

-- ## Subgroups

-- **ToDo**
-- `ℤ` as a subgroup of `ℚ`
example : AddSubgroup ℚ := sorry


-- **ToDo**
def Stupid (G : Type*) [Group G] : Subgroup G := sorry

-- **ToDo**
example : Stupid = ⊤ := sorry

-- ## Exercises

-- **Exercise**
example (G H : Type*) [AddGroup G] [AddGroup H] (f : G →+ H) : AddSubgroup G := sorry

-- **Exercise**
def conjugate {G : Type*} [Group G] (x : G) (H : Subgroup G) : Subgroup G := sorry


variable {G H K : Type*} [Group G] [Group H] [Group K]

open Subgroup

-- **Exercise**
example (φ : G →* H) (S T : Subgroup G) (hST : S ≤ T) : map φ S ≤ map φ T := by
  sorry

-- **Exercise**
example (φ : G →* H) (ψ : H →* K) (S : Subgroup G) :
    map (ψ.comp φ) S = map ψ (S.map φ) := by
  sorry


-- **Exercise**
/- For the next exercise, you might want to use the following results from the library:
`theorem Nat.card_eq_one_iff_exists : Nat.card α = 1 ↔ ∃ x : α, ∀ y : α, y = x := by ...`
as well as
`eq_bot_iff_forall`, whose content you might guess...
-/
lemma eq_bot_iff_card {A : Subgroup G} :
    A = ⊥ ↔ Nat.card A = 1 := by
  sorry


-- `⌘`


end Groups
section Rings

-- **ToDo**
#synth Ring ℤ
#synth CommRing ℤ
#synth Monoid ℤ
#synth AddMonoid ℤ
#check CommRing.toCommMonoid
#check CommRing.toAddCommGroupWithOne

-- **ToDo**
example (a b c : ℚ) : a + (b + c * 1) = a + b + c := by
  sorry

#check mul_one
#check add_assoc
#print AddMonoid
#print Field
#print CommMonoid


-- **ToDo**
example (R : Type*) [CommRing R] (x y : R) : (x + y)^2 = x^2 + 2 * x * y + y^2 := by
  sorry


-- `⌘`


variable {R S : Type*} [CommRing R] [CommRing S]

-- **ToDo**
example (f : R →+* S) (r : R) : IsUnit r → IsUnit (f r) := by
  sorry



-- **ToDo**
example (I : Ideal R) (x y : I) : I := by
  sorry


-- **ToDo**
example (I : Ideal R) (r : R) : r ∈ I → IsUnit r → I = ⊤ := by
  sorry


-- Show that the image of an ideal through a surjective ring homomorphism is again an ideal
-- **Exercise**
example (f : R →+* S) (I : Ideal R) (hf : Surjective f) : Ideal S := sorry




/- Show that the kernel of a ring homomorphism is an ideal: let's give it a French name so it does
not mix up with declarations in the library.
**Exercise** -/
def noyau (f : R →+* S) : Ideal R where
  carrier := {r : R | f r = 0}
  add_mem' := sorry
  zero_mem' := sorry
  smul_mem' := sorry


-- Show that if the ring homomorphism is injective, its kernel is `⊥`
-- **Exercise**
example (f : R →+* S) (hf : Injective f) : noyau f = ⊥ := by
  sorry


-- **Exercise**
example (f : R ≃+* S) (r : R) : IsUnit (f r) → IsUnit r := by
  sorry

end Rings
