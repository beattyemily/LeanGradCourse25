import Mathlib.GroupTheory.Subgroup.Center

section Monoids

open Function Set


-- In this example, both `1` and `*` are understood automatically
example (M : Type*) [Monoid M] (m : M) : m = m * 1 := by
  rw [mul_one]


-- @[to_additive]
lemma EqIfMulEq {M : Type*} [Monoid M] {a b c : M} (hba : b * a = 1) (hac : a * c = 1) :
    b = c := by
  rw [← one_mul c]
  rw [← hba]
  rw [mul_assoc]
  rw [hac]
  rw [mul_one b]

example : Monoid Bool where
  mul := Bool.and
  mul_assoc := by
    intro x y z
    exact Bool.and_assoc ..
  one := true
  one_mul := by
    intro t
    have := Bool.true_and t
    exact this
  mul_one := Bool.and_true


-- `⌘`


#synth Monoid Bool
#synth Monoid ℤ
#synth AddMonoid ℤ


-- `⌘`


-- example (M : Type*) [AddMonoid M] (a b c : M) (hba : b * a = 1) (hac : a * c = 1) : b = c := by
example (M : Type*) [AddMonoid M] (a b c : M) (hba : b + a = 0) (hac : a + c = 0) : b = c := by
  sorry
  -- apply EqIfMulEq
  -- apply EqIfAddEq hba hac

-- In general, `*`  and `+` are completely unrelated:
example (M : Type*) [Monoid M] [AddMonoid M] (a : M) : a * 1 = a + 0 := by
  rw [mul_one]
  rw [add_zero]

-- yet...
example (M : Type*) [Monoid M] [AddMonoid M] (a : M) : a * 0 = 0 := by
  -- rw [mul_zero]
  sorry

example (M: Type*) [Monoid M] [CommMonoid M] (m₁ m₂ m₃ : M) : m₁ * m₂ * m₃ = m₂ * (m₁ * m₃) := by
  sorry
  -- rw [mul_assoc]
  -- rw [mul_comm, mul_comm m₁ _]
  -- rw [← mul_assoc]


-- `⌘`


-- Observe how Lean understands automatically where `1` and `*` live
example (M N : Type*) [Monoid M] [Monoid N] (f : M →* N) : f 1 = 1 := by
  apply map_one


example (M N : Type*) [Monoid M] [CommMonoid N] (f : M →* N) (m₁ m₂ : M) (n : N) (h : f m₁ * n = 1) :
  f (m₁ * m₂) * n = f m₂ := by
  rw [map_mul]
  rw [mul_comm (f m₁) _]
  rw [mul_assoc]
  rw [h]
  rw [mul_one]


end Monoids

section Groups


example {G : Type*} [Group G] (x y z : G) : x * (y * z) * (x * z)⁻¹ * (x * y * x⁻¹)⁻¹ = 1 := by
  group

example {A : Type*} [AddCommGroup A] (a b : A) : a + 0 + b + 0 = b + a := by abel

-- `⌘`



example (G H : Type*) [Group G] [Group H] (f : G →* H) (g : G) : f (g⁻¹) = (f g)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one]
  rw [← map_mul]
  rw [inv_mul_cancel]
  apply map_one --try with `exact`: it does not work!
  -- exact MonoidHom.map_inv f g

noncomputable --what's this?
def IsoOfBijective (G H : Type*) [Group G] [Group H] (f : G →* H)
    (h_surj : Surjective f) (h_inj : Injective f) : G ≃* H := by
  fconstructor -- the difference between `constructor` and `fconstructor`
  · apply Equiv.ofBijective
    rw [Bijective]
    exact ⟨h_inj, h_surj⟩
  · intro g h
    simp only [Equiv.toFun_as_coe, Equiv.ofBijective_apply, map_mul]

-- ##Subgroups

-- `ℤ` as a subgroup of `ℚ`
example : AddSubgroup ℚ where
  carrier := Set.range ((↑) : ℤ → ℚ)
  add_mem' := by
    rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
    use n + m
    simp
  zero_mem' := by
    use 0
    simp
  neg_mem' := by
    rintro _ ⟨n, rfl⟩
    use -n
    simp

def Stupid (G : Type*) [Group G] : Subgroup G where --show the `_`-trick
  carrier := univ
  mul_mem' := by
    intro a b ha hb
    exact mem_univ (a * b) -- trivial
  one_mem' := by
    simp only
    exact mem_univ 1
  inv_mem' := fun _ ↦ mem_univ _

example : Stupid = ⊤ := rfl

example (G H : Type*) [AddGroup G] [AddGroup H] (f : G →+ H) : AddSubgroup G where
  carrier := {g : G | f g = 0}
  add_mem' := by
    intro a b ha hb
    rw [Set.mem_setOf]
    rw [map_add]
    rw [hb]
    rw [ha]
    rw [zero_add]
  zero_mem' := by
    rw [Set.mem_setOf]
    apply map_zero
  neg_mem' := by
    intro x hx
    simp only
    rw [Set.mem_setOf]
    rw [map_neg]
    rw [hx]
    rw [neg_zero]

-- one more example, then some exercices copied from `Solutions_S01_Goups.lean` and let's pass to rings
-- yes
def conjugate {G : Type*} [Group G] (x : G) (H : Subgroup G) : Subgroup G where
  carrier := {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹}
  one_mem' := by
    dsimp
    use 1
    constructor
    exact H.one_mem
    group
  inv_mem' := by
    dsimp
    rintro - ⟨h, h_in, rfl⟩
    use h⁻¹, H.inv_mem h_in
    group
  mul_mem' := by
    dsimp
    rintro - - ⟨h, h_in, rfl⟩ ⟨k, k_in, rfl⟩
    use h*k, H.mul_mem h_in k_in
    group

variable {G H : Type*} [Group G] [Group H]

section Rings

end Rings
