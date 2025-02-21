import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


variable (P Q R S : Prop)

-- **ToDo**
example (n : ℕ) (hn : n ≤ 3) : n ≤ 5 := by
  apply le_trans
  use hn
  linarith


-- `⌘`


/- # The Prop type -/

#check 2
#check ℕ
#check 2 < 3
#check 37 < 1
#check True
#check trivial
#check true
#check Bool


-- '⌘'


/- # exact, intro, apply, rfl-/

-- Use of the `exact` tactic
-- **ToDo**
example (hP : P) : P := by
  exact hP

-- Use of the `intro` tactic
-- **ToDo**
example : P → P := by
  intro hP
  exact hP

-- Use of the `apply` tactic
-- **ToDo**
example (h : P → Q) (hP : P) : Q := by
  apply h
  exact hP

-- Use `\.` to write `·`
-- **ToDo**
example : (P → Q → R) → ((P → Q) → (P → R)) := by
  intro h1
  intro h2
  intro hP
  apply h1
  · exact hP
  · apply h2
    exact hP


-- Modus Ponens: if `P → Q` then `Q` can be deduced from `P`
-- **Exercise**
example : P → (P → Q) → Q := by
  intro hP h
  apply h
  exact hP

-- Transitivity of `→`
-- **Exercise**
example : (P → Q) → (Q → R) → P → R := by
  intro h1 h2 hP
  apply h2
  apply h1
  exact hP

-- Use of the `rfl` tactic
-- **ToDo**
example : P = P := by
  rfl

-- **Exercise**
example (hP : P) : Q → (hP = hP) := by
  intro
  rfl

-- **Exercise**
example (hP : P) : R → P → Q → (hP = hP) := by
  intro _ _ _
  rfl


-- `⌘`


-- # `rw`

-- `P` is not a proposition: it is a True/False statement for terms in `α`.
-- **ToDo**
example (α : Type) (P : α → Prop) (x y : α) (hx : P x) (h : y = x) : P y := by
  rw [h]
  exact hx


-- **ToDo**
example (α : Type) (P Q : α → Prop) (x : α) (hP : P x) (h : P = Q) : Q x := by
  rw [← h] -- Use `\l` to write `←`
  exact hP

-- **Exercise**
example (n : ℕ) (h : n = 5) : n = 2 + 3 := by
  rw [h]

-- **Exercise**
example (n m : ℕ) (hn : n = 5) (hm : 11 = m) : m = n + 6 := by
  rw [hn, ← hm]

-- **Exercise**
example (α : Type) (a b c : α) (H : (a = b) → P ) (h1 : c = a) (h2 : b = c) : P := by
  apply H
  rw [h2]
  rw [← h1]
  -- exact h2


-- `⌘`


/- # `True`, `False`, negation, contradiction -/

-- **ToDo**
example : True := by
  exact trivial

-- **Exercise**
example : True → True := by
  intro h
  exact h

-- Use of the `exfalso` tactic
-- **ToDo**
example : False → P := by
  intro h
  exfalso
  exact h

-- **Exercise**
example : (P → False) → P → Q := by
  intro h hP
  exfalso
  apply h
  exact hP

-- type `¬` by typing `\not`.
-- **ToDo**
example : P → Q → P → ¬ Q → ¬ P := by
  intro hp hq hp' h_neq abs
  apply h_neq
  exact hq

-- **Exercise**
example : P → ¬ P → False := by
  intro hP hneP
  apply hneP
  exact hP

-- Use of the `by_contra` tactic
-- **ToDo**
example : (¬Q → ¬P) → P → Q := by
  intro h1 hP
  by_contra h2
  have h3 := h1 h2
  exact h3 hP

-- **Exercise**
example : (P → ¬ Q) → (Q → ¬ P) := by
  intro t_to_f h_neQ
  by_contra h
  have H := t_to_f h
  apply H
  exact h_neQ

-- **Exercise**
example (h : ¬ (2 = 2)) : P → Q := by
  by_contra
  -- exfalso
  apply h
  rfl


-- `⌘`


/- # Conjunction / And
  Use `\and` to write `∧` -/

-- **ToDo**
example : P → Q → P ∧ Q := by
  intro hP hQ
  constructor
  · exact hP
  · exact hQ

-- **ToDo**
example : P ∧ Q → P := by
  intro h
  exact h.left

-- **Exercise**
example : P ∧ Q → Q := by
  intro h
  exact h.2

-- **Exercise**
example : (P → Q → R) → P ∧ Q → R := by
  intro h1 h2
  apply h1
  · exact h2.1
  · exact h2.2

-- `∧` is symmetric
-- **Exercise**
example : P ∧ Q → Q ∧ P := by
  intro h
  constructor
  · exact h.right
  · exact h.1


-- `∧` is transitive
-- **Exercise**
example : P ∧ Q → Q ∧ R → P ∧ R := by
  intro h1 h2
  constructor
  · exact h1.1
  · exact h2.2

-- **Exercise**
example : False → P ∧ False := by
  intro h
  exfalso
  exact h

-- **Exercise**
example : (P ∧ Q → R) → P → Q → R := by
  intro h hP hQ
  apply h
  constructor
  · exact hP
  · exact hQ

/-  # Disjunction / Or
  Use `\or` to write `∨` -/

-- **ToDo**
example : P → P ∨ Q := by
  intro hP
  left
  exact hP

-- **Exercise**
example : Q → P ∨ Q := by
  intro hQ
  right
  exact hQ

/- **ToDo**
  symmetry of `∨`, and use of `assumption`  -/
example : P ∨ Q → Q ∨ P := by
  intro h
  cases h
  · right
    assumption
  · left
    assumption

/- **ToDO**
   the result of `cases` can be given explicit names, by using `rcases ? with ?1 | ?h2 `-/
example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro h1 h2 h3
  rcases h1 with h | h
  · apply h2
    exact h
  · apply h3
    exact h

/- **ToDO**
  use of the `by_cases` tactic. -/
example : R ∨ ¬ R := by
  by_cases hR : R
  · left
    exact hR
  · right
    exact hR


-- associativity of `∨`
-- **Exercise**
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  constructor
  · intro h
    rcases h with h1 | h2
    · rcases h1 with h11 | h12
      · left
        exact h11
      · right
        left
        exact h12
    · right
      right
      exact h2
  · intro h
    rcases h with h1 | h2
    · left
      left
      exact h1
    · rcases h2 with h21 | h22
      · left
        right
        exact h21
      · right
        exact h22


-- **Exercise**
example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  intro h1 h2 h3
  rcases h3 with h31 | h32
  · left
    exact h1 h31
  · right
    exact h2 h32


-- **Exercise**
example : (P → Q) → P ∨ R → Q ∨ R := by
  intro h1 h2
  rcases h2 with h21 | h22
  · left
    exact h1 h21
  · right
    exact h22


-- `⌘`


/- # Equivalence
    Use `\iff` to write `↔` -/

-- **ToDO**
example : P ↔ P := by
  constructor
  · intro hP
    exact hP
  · intro hP
    exact hP

-- **ToDO**
lemma lemma1 : (P ↔ Q) → (Q ↔ P) := by
  intro h
  -- rcases h with h1 | h2
  constructor
  · exact h.2
  · exact h.1

-- **ToDO**
example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor
  · exact lemma1 P Q
  · exact lemma1 Q P

-- **Exercise**
example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro h1 h2
  constructor
  · intro hP
    exact h2.1 (h1.1 hP)
  · intro hR
    exact h1.2 (h2.2 hR)

-- **Exercise**
example : ¬(P ↔ ¬P) := by
  intro h
  have hP := h.1
  have hneP := h.2
  apply hP
  · apply hneP
    intro h_abs
    apply hP h_abs
    exact h_abs
  · apply hneP
    intro h_abs
    apply hP h_abs
    exact h_abs

-- **Exercise**
example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by
  intro h1 h2
  constructor
  · intro h3
    rcases h3 with h31 | h32
    · left
      exact h1.1 h31
    · right
      exact h2.1 h32
  · intro h_imp
    cases h_imp
    · left
      apply h1.2
      assumption
    · right
      apply h2.2
      assumption


-- `⌘`


variable (α : Type*) (p q : α → Prop) -- Use `\alpha` to write `α`

/-
  # Quantifiers
  Use `\forall` and `\exists` to write `∀` and `∃`. -/

-- **ToDO**
example (h : ∀ x : α, p x) (y : α) : p y := by
  specialize h y
  exact h

-- **Exercise** (remember the `by_cases` tactic!)
example : (∀ x, p x ∨ R) ↔ (∀ x, p x) ∨ R := by
  constructor
  · intro h
    by_cases hR : R
    · right
      exact hR
    · left
      intro x
      specialize h x
      cases h
      · assumption
      · exfalso
        exact hR (by assumption)
  · intro h
    intro x
    by_cases hR : R
    · right
      exact hR
    · left
      rcases h with h1 | h2
      · specialize h1 x
        exact h1
      · exfalso
        exact hR h2


-- **Exercise**
example : (∀ x : α, p x ∧ q x) → ∀ x : α, p x := by
  intro h
  intro x
  exact (h x).left

/- **ToDO**
    - Use of the `use` tactic -/
example (x : α) (h : p x) : ∃ y, p y := by
  use x

/- **ToDO**
    - Use of the `obtain` tactic -/
example (h : ∃ x, p x ∧ q x) : ∃ x, q x := by
  obtain ⟨x, hx⟩ := h
  use x
  exact hx.2

-- **Exercise**
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x := by
  obtain ⟨x, hx⟩  := h
  use x
  constructor
  · exact hx.2
  · exact hx.1


-- **Exercise**
example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
  constructor
  · intro h
    constructor
    · intro x
      exact (h x).left
    · intro x
      exact (h x).right
  · intro h x
    constructor
    · exact h.left x
    · exact h.right x

-- **Exercise**
example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by
  intro h1 h2 x
  apply h1 x
  exact h2 x

-- **Exercise**
example (h : ¬ ∃ x, ¬ p x) : ∀ x, p x := by
  intro x
  by_contra h2
  have h3 : ∃ x, ¬ p x := by
    use x
  exact h h3

/- **ToDO**
    - Use of the `rintro` tactic -/
example : (∃ _ : α, R) → R := by
  rintro ⟨x, hx⟩
  exact hx


-- **Exercise**
example (x : α) : R → (∃ _ : α, R) := by
  intro hR
  use x

-- **Exercise**
example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by
  constructor
  · rintro h ⟨x, hx⟩
    apply hx
    exact h x
  · intro H x
    by_contra h_abs
    apply H
    use x

/- **ToDO**
    - Use of the `contrapose` tactic, changing `P → Q` to `¬ Q → ¬ P`.
    Its extension `contrapose!` pushes negations from the head of a quantified expression
    to its leaves. -/
example (a : α) : (∃ x, p x → R) ↔ ((∀ x, p x) → R) := by
  constructor
  · intro h1 h2
    obtain ⟨x, hx⟩ := h1
    apply hx
    exact h2 x
  · contrapose!
    intro h
    constructor
    · intro x
      exact (h x).left
    · specialize h a
      exact h.right


-- **Exercise**
example (a : α) : (∃ x, R → p x) ↔ (R → ∃ x, p x) := by
  constructor
  · rintro ⟨x, hx⟩ hR
    use x
    exact hx hR
  · contrapose!
    intro h
    constructor
    · specialize h a
      exact h.left
    · intro x
      specialize h x
      exact h.right
