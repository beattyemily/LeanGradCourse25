import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Operations
import Mathlib.Data.Set.Insert
import Mathlib.Order.SetNotation
import Mathlib.Tactic.Common

open Set Classical

-- # §1: Sets

open scoped Set
section Definitions


-- **An error**
-- example (S : Set) := sorry
example {α : Type} (S : Set α) : S = S := rfl

-- **A tautology**

-- **ToDo**
example (α : Type) (x : α) (S : Set α) : x ∈ S ↔ S x := by
  rfl


-- **The positive integers**
-- **ToDo**
def PositiveIntegers : Set ℤ := (fun n ↦ n > 0)

-- `⌘`

-- **ToDo**
lemma one_posint : 1 ∈ PositiveIntegers := by
  apply Int.one_pos

-- **ToDo**
def PositiveNaturals : Set ℕ := by
  exact (0 < ·)

-- **ToDo**
example : 1 ∈ PositiveNaturals := by
  apply Nat.one_pos

-- **ToDo**
-- Why does this *fail*? How to fix it?
example : (-1) ∉ PositiveIntegers := by
  intro h
  replace h := h.out
  exact (Int.negSucc_not_nonneg (0 + 0).succ).mp (by exact h)
  -- this used exact?. exact? searches the whole library to see if there is a lemma which matches it. The additional "(by exact h)" instead of just "h" allows for a little bit of simplification.
  -- we could also have used omega. omega is a small tactic that can do basic arithmetic: everything must be linear, but it can do addition, comparison, etc.

-- **The even naturals**

-- **ToDo?**
def EvenNaturals : Set ℕ := (fun n ↦ n % 2 = 0) -- n mod 2 = 0.

-- **ToDo?**
example (n : ℕ) : n ∈ EvenNaturals → (n+2) ∈ EvenNaturals := by
  intro hn
  replace hn := hn.out
  rw [mem_def]
  rw [← Nat.add_mod_right] at hn
  exact hn


-- **An abstract set**

-- **ToDo**
def AbstractSet {α : Type} (P : α → Prop) : Set α := P
def AbstractSet' {α : Type} (P : α → Prop) : Set α := setOf P

-- **ToDo**
-- The same, but it is a general principle that the second version is better
example {α : Type} (P : α → Prop) : AbstractSet P = AbstractSet' P := by
  rfl


-- `⌘`

-- **ToDo**
-- **Subsets as implication**
example {α : Type} (S T : Set α) (s : α) (hST : S ⊆ T) (hs : s ∈ S) : s ∈ T := by
  apply hST
  exact hs


-- `⌘`


-- **A double inclusion**

-- **ToDo**
example (α : Type) (S T W : Set α) (hST : S ⊆ T) (hTW : T ⊆ W) : S ⊆ W := by
  intro x
  intro hx
  apply hTW
  apply hST
  exact hx

-- **Another take on subsets and sets as types**

-- **ToDo**
def subsub {α : Type} {S : Set α} (P : S → Prop) : Set (S : Type) := by
  exact P

-- **ToDo**
def subsub' {α : Type} {S : Set α} (P : α → Prop) : Set (S : Type) := by
  intro a
  exact P a


-- Are they *equal*? This is an exercise below.

-- **ToDo**
-- Why does this *fail*? How to fix it?
example (α : Type) (S : Set α) (P : S → Prop) (x : ↑S) (_ : x ∈ subsub P) : x.1 ∈ S := by -- terms of type ↑S are pairs, where the first term has type alpha and the second term is a witness that the first term satisfies the defining property of S.
  exact x.2


-- **What is really this "injection"  `Set α ↪ Type`?**

-- **ToDo?**
-- Why does this *fail*? How to fix it?
-- n.val and n.1 are the same
example : ∀ n : PositiveIntegers, 0 < n.val := by
  rintro ⟨ a, ha ⟩
  exact ha

-- `⌘`


/- **§ Some exercises** -/

-- **Exercise**
example : 1 ∉ EvenNaturals := by
  intro h
  replace h := h.out
  omega

-- **Exercise**
example : -1 ∉ PositiveIntegers := by
  intro h
  replace h := h.out
  omega

-- **Exercise**
-- Define the set of even, positive numbers
def EvenPositiveNaturals : Set PositiveIntegers := (fun n ↦ n.1 % 2 = 0)

-- **Exercise**
-- Why does this *fail*? How to fix it? Fails because the type of 1 is integer but the type of EvenPositiveNaturals is PositiveIntegers
example : ∀ n : EvenPositiveNaturals, n.1.1 = 1 → False := by
  rintro ⟨ ⟨ nv, hn ⟩, hnv ⟩
  intro h
  simp at h
  replace hnv := hnv.out
  simp at hnv
  omega

-- **Exercise**
-- Define the set of odd numbers and prove some properties
def OddNaturals : Set ℕ := (fun n ↦ n % 2 = 1)

-- **Exercise**
example : 3 ∈ OddNaturals := by
  exact rfl


-- **Exercise**
lemma lemma1 (n : ℕ) : n ∈ OddNaturals ↔ n ∉ EvenNaturals := by
  constructor
  · intro hno hne
    replace hno := hno.out
    replace hne := hne.out
    omega
  · intro h
    rw [mem_def, OddNaturals]
    rw [mem_def, EvenNaturals] at h
    omega


-- **Exercise**
-- Why does this *fail*?
-- example (α : Type) (S : Set α) : subsub = subsub' := sorry


end Definitions

-- ## Operations on sets

section Operations

-- **Self-intersection is the identity, proven with extensionality**

-- **ToDo**
example (α : Type) (S : Set α) : S ∩ S = S := by
  ext x
  constructor
  · rintro ⟨ hxSSl, hxSSr ⟩
    exact hxSSl
  · intro hxS
    constructor
    · exact hxS
    · exact hxS


-- `⌘`


-- **The union**
-- **ToDo**
example (α : Type) (S T : Set α) (H : S ⊆ T) : S ∪ T = T := by
  ext x
  constructor
  · intro h
    cases h
    · apply H
      assumption
    · assumption
  · intro h
    right
    assumption


-- **An _unfixable_ problem**
-- **ToDo**
-- example (α β : Type) (S : Set α) (T : Set β) : S ⊆ S ∪ T := sorry
/- *Sol.:*  Well, it was unfixable, so there is no solution...-/


-- `⌘`


-- **Empty set**

-- **ToDo**
example : (setOf (0 < ·) : Set ℤ) ∩ setOf (· < 0) = ∅ := by
  ext x
  constructor
  · rintro ⟨ hxpos, hxneg ⟩
    rw [mem_setOf_eq] at hxpos
    rw [mem_setOf_eq] at hxneg
    omega
  · intro h
    tauto


-- `⌘`


-- **§ Indexed unions**

-- **ToDo**
example {α I : Type} (A : I → Set α) (x : α) : x ∈ ⋃ i, A i ↔ ∃ i, x ∈ A i := by
  constructor
  · intro h
    rw [mem_iUnion] at h
    exact h
  · simp

/- **§ Some exercises** -/

-- **Exercise**
-- Try to prove the statement proven before but without using the library
example (α : Type) (S T : Set α) (H : S ⊆ T) : T = S ∪ T := by
  ext x
  constructor
  · intro hx
    right
    exact hx
  · intro k
    rcases k
    · apply H
      assumption
    · assumption

-- **Exercise**
example (α : Type) (S T R : Set α) : S ∩ (T ∪ R) = (S ∩ T) ∪ (S ∩ R) := by
  aesop
  -- ext x
  -- constructor
  -- · rintro ⟨ hS, hT | hR ⟩
  --   · left
  --     exact ⟨ hS, hT ⟩
  --   · right
  --     exact ⟨ hS, hR ⟩
  -- · intro h
  --   rcases h with ⟨ hS, hT ⟩ | ⟨ hS', hR ⟩
  --   · constructor
  --     · exact hS
  --     · left
  --       exact hT
  --   · constructor
  --     · exact hS'
  --     · right
  --       exact hR



-- **Exercise**
example (α : Type) (S : Set α) : Sᶜ ∪ S = univ := by
  ext x
  constructor
  · tauto
  · intro h
    by_cases hx : (x ∈ S)
    · right
      exact hx
    · left
      tauto

-- **Exercise**
-- For this, you can try `simp` at a certain point...`le_antisymm` can also be useful.
example : (setOf (0 ≤ ·) : Set ℤ) ∩ setOf (· ≤ 0) = {0} := by
  ext x
  constructor
  · intro h
    simp
    simp at h
    omega
  · intro h
    constructor
    · simp
      simp at h
      omega
    · simp
      simp at h
      omega

-- **Exercise**
-- Using your definition of `OddNaturals` prove the following:
example : EvenNaturals ∪ OddNaturals = univ := by
  ext x
  constructor
  · intro h
    tauto
  · intro h
    by_cases hx : (x ∈ EvenNaturals)
    · left
      exact hx
    · right
      rw [mem_def, OddNaturals]
      rw [mem_def, EvenNaturals] at hx
      omega


-- **Exercise**
-- A bit of difference, inclusion and intersection
example (α : Type) (S T : Set α) (h : T ⊆ S) : T \ S = ∅ := by
  ext x
  constructor
  · rintro ⟨ hT, hSc ⟩
    exfalso
    tauto
  · tauto


-- **Exercise**
example (α : Type) (S T R : Set α) : S \ (T ∪ R) ⊆ (S \ T) \ R := by
  intro x
  rintro ⟨ hS, hcTuR ⟩
  constructor
  · constructor
    · exact hS
    · simp at hcTuR
      exact hcTuR.left
  · simp at hcTuR
    exact hcTuR.right



-- **Exercise**
-- Indexed intersections work as indexed unions (_mutatis mutandis_)
example {α I : Type} (A B : I → Set α) : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
  ext x
  constructor
  · intro h
    constructor
    · simp at h
      simp
      intro i
      specialize h i
      exact h.left
    · simp at h
      simp
      intro i
      specialize h i
      exact h.right
  · rintro ⟨ hA, hB ⟩
    simp
    simp at hA hB
    intro i
    constructor
    · specialize hA i
      exact hA
    · specialize hB i
      exact hB


-- **Exercise**
example {α I : Type} (A : I → Set α) (S : Set α) : (S ∩ ⋃ i, A i) = ⋃ i, A i ∩ S := by
  ext x
  constructor
  · rintro ⟨ hS, hei ⟩
    simp
    simp at hei
    obtain ⟨ y, hy ⟩ := hei
    constructor
    · use y
    · exact hS
  · intro h
    simp
    simp at h
    obtain ⟨ h1 , h2 ⟩ := h
    constructor
    · exact h2
    · obtain ⟨ y, hy ⟩ := h1
      use y

end Operations


-- `⌘`


-- # §2: Functions

-- **ToDo**
-- Functions do not natively act on elements of sets: how can we fix this code?
example (α β : Type) (S : Set α) (T : Set β) (f g : S → β) :
  f = g ↔ ∀ a : α, (ha : a ∈ S) → f ⟨ a, ha ⟩  = g ⟨ a, ha ⟩ := by
    constructor
    · intro h
      simp [h]
    · intro h
      ext x
      tauto


-- `⌘`


section Operations

open Function

variable (α β : Type) (f : α → β)

-- The **image**

-- **ToDo**
example : 1 ∈ Nat.succ '' univ := by
  sorry

-- **ToDo**
-- We can upgrade a function `f` to a function between sets, using its *image*:
example : Set α → Set β := by
  sorry


-- Observe that `obtain` does not work here
-- **ToDo**
noncomputable example (b : β) (hf : Surjective f) : α := by -- need to invoke the axiom of choice here
  have hn := hf b
  let a := (hn).choose
  have ha := (hn).choose_spec
  use a

-- **ToDo**
example (α β: Type) (f : α → β) (S : Set α) : S ≠ ∅ → f '' S ≠ ∅ := by
  sorry


-- `⌘`


-- The **preimage**

-- **ToDo**
example : 2 ∈ Nat.succ ⁻¹' {2, 3} ∧ 1 ∉ .succ ⁻¹' {0, 3} := by
  sorry

-- `⌘`

-- **ToDo**
example : InjOn (fun n : ℤ ↦ n ^ 2) PositiveIntegers := by
  sorry




/- **§ Some exercises** -/

open Function

-- **Exercise**
/- The range is not *definitionally equal* to the image of the universal set:
  use extensionality! -/
example : range f = f '' univ := by
  sorry

-- **Exercise**
-- Why does this code *fail*? Fix it, and then prove the statement
example (N : OddNaturals) : N ∈ Nat.succ '' (EvenNaturals) := sorry

-- **Exercise**
-- Why does this code *fail*? Fix it, and then prove the statement
example (N : OddNaturals) :  N ∈ Nat.succ ⁻¹' (EvenNaturals) := by sorry

-- **Exercise**
-- Not every `n : ℕ` is the successor or something...
example : range Nat.succ ≠ univ := by
  sorry


-- **Exercise**
/- The following is a *statement* and not merely the *definition* of being injective;
  prove it. -/
example : Injective f ↔ InjOn f univ := by
  sorry


-- **Exercise**
/- The complement `Sᶜ` is referred to with the abbreviation `compl` in the library -/
example : Surjective f ↔ (range f)ᶜ = ∅ := by
  sorry

end Operations
