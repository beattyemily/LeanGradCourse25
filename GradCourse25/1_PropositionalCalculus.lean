import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


variable (P Q R S : Prop)

-- **ToDo**
example (n : ℕ) (hn : n ≤ 3) : n ≤ 5 := by
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
  intro PimpQimpR PimpQ hP
  apply PimpQimpR
  · exact hP
  · apply PimpQ
    exact hP


-- Modus Ponens: if `P → Q` then `Q` can be deduced from `P`
-- **Exercise**
example : P → (P → Q) → Q := by
  intro hP PimpQ
  apply PimpQ
  exact hP

-- Transitivity of `→`
-- **Exercise**
example : (P → Q) → (Q → R) → P → R := by
  intro PimpQ QimpR hP
  apply QimpR
  apply PimpQ
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
  intros
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
  rw [← h]
  exact hP

-- **Exercise**
example (n : ℕ) (h : n = 5) : n = 2 + 3 := by
  rw [h]

-- **Exercise**
example (n m : ℕ) (hn : n = 5) (hm : 11 = m) : m = n + 6 := by
  rw [hn]
  rw [← hm]

-- **Exercise**
example (α : Type) (a b c : α) (H : (a = b) → P ) (h1 : c = a) (h2 : b = c) : P := by
  apply H
  rw [← h1]
  rw [h2]

-- `⌘`


/- # `True`, `False`, negation, contradiction -/

-- **ToDo**
example : True := by
  trivial
-- **Exercise**
example : True → True := by
  intro
  trivial

-- Use of the `exfalso` tactic
-- **ToDo**
example : False → P := by
  intro h
  exfalso
  exact h

-- **Exercise**
example : (P → False) → P → Q := by
  intro PimpF hP
  exfalso
  apply PimpF
  exact hP

-- type `¬` by typing `\not`.
-- **ToDo**
example : P → Q → P → ¬ Q → ¬ P := by
  intro hP hQ hP' hnQ habs
  apply hnQ
  exact hQ

-- **Exercise**
example : P → ¬ P → False := by
  intro hP hnP
  apply hnP
  exact hP

-- Use of the `by_contra` tactic
-- **ToDo**
example : (¬Q → ¬P) → P → Q := by
  intro h hP
  by_contra h_abs
  apply h
  · exact h_abs
  · exact hP

-- **Exercise**
example : (P → ¬ Q) → (Q → ¬ P) := by
  intro PimpnQ hQ
  by_contra h_abs
  apply PimpnQ
  · exact h_abs
  · exact hQ


-- **Exercise**
example (h : ¬ (2 = 2)) : P → Q := by
  intro hP
  by_contra h_abs
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
  intro hPaQ
  exact hPaQ.left

-- **Exercise**
example : P ∧ Q → Q := by
  intro hPaQ
  exact hPaQ.right

-- **Exercise**
example : (P → Q → R) → P ∧ Q → R := by
  intro PimpQimpR hPaQ
  sorry

-- `∧` is symmetric
-- **Exercise**
example : P ∧ Q → Q ∧ P := by sorry


-- `∧` is transitive
-- **Exercise**
example : P ∧ Q → Q ∧ R → P ∧ R := by sorry

-- **Exercise**
example : False → P ∧ False := by sorry

-- **Exercise**
example : (P ∧ Q → R) → P → Q → R := by sorry

/-  # Disjunction / Or
  Use `\or` to write `∨` -/

-- **ToDo**
example : P → P ∨ Q := by sorry

-- **Exercise**
example : Q → P ∨ Q := by sorry

/- **ToDo**
  symmetry of `∨`, and use of `assumption`  -/
example : P ∨ Q → Q ∨ P := by sorry

/- **ToDO**
   the result of `cases` can be given explicit names, by using `rcases ? with ?1 | ?h2 `-/
example : P ∨ Q → (P → R) → (Q → R) → R := by sorry


/- **ToDO**
  use of the `by_cases` tactic. -/
example : R ∨ ¬ R := by sorry


-- associativity of `∨`
-- **Exercise**
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by sorry


-- **Exercise**
example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by sorry


-- **Exercise**
example : (P → Q) → P ∨ R → Q ∨ R := by sorry


-- `⌘`


/- # Equivalence
    Use `\iff` to write `↔` -/

-- **ToDO**
example : P ↔ P := by sorry

-- **ToDO**
lemma lemma1 : (P ↔ Q) → (Q ↔ P) := by sorry

-- **ToDO**
example : (P ↔ Q) ↔ (Q ↔ P) := by sorry

-- **Exercise**
example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by sorry

-- **Exercise**
example : ¬(P ↔ ¬P) := by sorry

-- **Exercise**
example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by sorry


-- `⌘`


variable (α : Type*) (p q : α → Prop) -- Use `\alpha` to write `α`

/-
  # Quantifiers
  Use `\forall` and `\exists` to write `∀` and `∃`. -/

-- **ToDO**
example (h : ∀ x : α, p x) (y : α) : p y := by sorry

-- **Exercise** (*remember* the `by_cases` tactic!)
example : (∀ x, p x ∨ R) ↔ (∀ x, p x) ∨ R := by sorry


-- **Exercise**
example : (∀ x : α, p x ∧ q x) → ∀ x : α, p x := by sorry

/- **ToDO**
    - Use of the `use` tactic -/
example (x : α) (h : p x) : ∃ y, p y := by sorry

/- **ToDO**
    - Use of the `obtain` tactic -/
example (h : ∃ x, p x ∧ q x) : ∃ x, q x := by sorry

-- **Exercise**
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x := by sorry


-- **Exercise**
example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by sorry

-- **Exercise**
example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by sorry


-- **Exercise**
example (h : ¬ ∃ x, ¬ p x) : ∀ x, p x := by sorry

/- **ToDO**
    - Use of the `rintro` tactic -/
example : (∃ x : α, R) → R := by sorry


-- **Exercise**
example (x : α) : R → (∃ x : α, R) := by sorry

-- **Exercise**
example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by sorry

/- **ToDO**
    - Use of the `contrapose` tactic, changing `P → Q` to `¬ Q → ¬ P`.
    Its extension `contrapose!` pushes negations from the head of a quantified expression
    to its leaves. -/
example (a : α) : (∃ x, p x → R) ↔ ((∀ x, p x) → R) := by sorry


-- **Exercise**
example (a : α) : (∃ x, R → p x) ↔ (R → ∃ x, p x) := by sorry
