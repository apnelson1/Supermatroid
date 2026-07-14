import Mathlib.Order.ModularLattice

open OrderDual

variable {α : Type*} [Lattice α] {a b c x y z : α}


section perspective

def RelPerspective (x a b : α) := a ⊓ x = b ⊓ x ∧ a ⊔ x = b ⊔ x

lemma RelPerspective.toDual (h : RelPerspective x a b) :
    RelPerspective (toDual x) (toDual a) (toDual b) :=
  ⟨h.2, h.1⟩

lemma RelPerspective.ofDual {x a b : αᵒᵈ} (h : RelPerspective x a b) :
    RelPerspective (ofDual x) (ofDual a) (ofDual b) :=
  ⟨h.2, h.1⟩

lemma RelPerspective.sup_eq (h : RelPerspective x a b) : a ⊔ x = b ⊔ x := h.2

lemma RelPerspective.sup_eq' (h : RelPerspective x a b) : x ⊔ a = x ⊔ b := by
  rw [sup_comm, h.sup_eq, sup_comm]

lemma RelPerspective.inf_eq (h : RelPerspective x a b) : a ⊓ x = b ⊓ x := h.1

lemma RelPerspective.inf_eq' (h : RelPerspective x a b) : x ⊓ a = x ⊓ b :=
  h.toDual.sup_eq'

lemma RelPerspective.refl : RelPerspective x a a := ⟨rfl,rfl⟩

lemma RelPerspective.symm (h : RelPerspective x a b) : RelPerspective x b a :=
  ⟨h.1.symm, h.2.symm⟩

lemma RelPerspective.trans (h : RelPerspective x a b) (h' : RelPerspective x b c) :
    RelPerspective x a c :=
  ⟨h.1.trans h'.1, h.2.trans h'.2⟩

lemma relPerspective_iff_of_le_le (haxb : a ⊓ x ≤ b) (habx : a ≤ b ⊔ x) :
    RelPerspective x a b ↔ b ⊓ x ≤ a ∧ b ≤ a ⊔ x := by
  simp [RelPerspective, le_antisymm_iff, habx, haxb]

lemma RelPerspective.mono_right (h : RelPerspective x a b) (hac : a ≤ c) (hcb : c ≤ b) :
    RelPerspective x a c :=
  ⟨(inf_le_inf_right _ hac).antisymm ((inf_le_inf_right _ hcb).trans (by rw [h.inf_eq])),
    (sup_le_sup_right hac _).antisymm ((sup_le_sup_right hcb _).trans (by rw [h.sup_eq]))⟩

lemma RelPerspective.mono_left (h : RelPerspective x a b) (hac : a ≤ c) (hcb : c ≤ b) :
    RelPerspective x b c :=
  (h.symm.toDual.mono_right hcb hac).ofDual

variable [IsModularLattice α]

lemma RelPerspective.eq_of_le (h : RelPerspective x a b) (hab : a ≤ b) : a = b :=
  eq_of_le_of_inf_le_of_sup_le hab h.inf_eq.symm.le h.sup_eq.symm.le



-- lemma RelPerspective.mono_right' (h : RelPerspective x a c) (hab : a ⊓ x ≤ b) (hbc : b ≤ c) :
--     RelPerspective x a b :



end perspective

section union_inter

variable [IsModularLattice α]

-- lemma eq_of_le_of_inf_le_of_le_sup (hxy : x ≤ y) (hi : y ⊓ z ≤ x) (hu : y ≤ x ⊔ z) : x = y := by
--   refine hxy.antisymm ?_
--   rw [← inf_eq_right, sup_inf_assoc_of_le _ hxy] at hu
--   rwa [← hu, sup_le_iff, and_iff_right rfl.le, inf_comm]

-- example (hxy : x ≤ y) (hi : y ⊓ z ≤ x ⊓ z) (hu : y ⊔ z ≤ x ⊔ z) : x = y := by
--   refine hxy.antisymm ?_
--   calc y = (y ⊔ z) ⊓ y := Eq.symm <| inf_eq_right.2 le_sup_left
--        _ ≤ (x ⊔ z) ⊓ y := inf_le_inf_right _ hu
--        _ = x ⊔ (z ⊓ y) := sup_inf_assoc_of_le _ hxy
--        _ ≤ x ⊔ (y ⊓ z) := by rw [inf_comm]
--        _ ≤ x ⊔ (x ⊓ z) := sup_le_sup_left hi _
--        _ = x           := sup_of_le_left inf_le_left


end union_inter

section distrib

/-- A distributive triple in a modular lattice is a triple `x y z` that obeys any form of the
  distributive law. Modularity of the lattice gives that one form implies them all. -/
def DistribOn (x y z : α) := x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z)

theorem distribOn_iff_sup_inf : DistribOn x y z ↔ x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z) := Iff.rfl

theorem distribOn_of_sup_inf_sup_le (h : (x ⊔ y) ⊓ (x ⊔ z) ≤ x ⊔ (y ⊓ z)) : DistribOn x y z :=
  h.antisymm' (le_inf (sup_le_sup_left inf_le_left _) (sup_le_sup_left inf_le_right _))

theorem DistribOn.sup_inf_left (h : DistribOn x y z) : x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z) :=
  h

theorem DistribOn.symm_right (h : DistribOn x y z) : DistribOn x z y := by
  rw [DistribOn, inf_comm, h.sup_inf_left, inf_comm]

theorem distribOn_of_le_sup_inf (h : z ≤ x ⊔ y ⊓ z) : DistribOn x y z :=
  distribOn_of_sup_inf_sup_le (inf_le_right.trans (sup_le le_sup_left h))

variable [IsModularLattice α]

theorem DistribOn.inf_sup_right (h : DistribOn x y z) : (x ⊔ y) ⊓ z = (x ⊓ z) ⊔ (y ⊓ z) := by
  rw [sup_comm (x ⊓ z), IsModularLattice.inf_sup_inf_assoc, sup_comm _ x,
    show (_ ⊓ z = _ ⊓ z) from congr_arg (· ⊓ z) h, inf_assoc, inf_of_le_right (b := z) le_sup_right]

theorem DistribOn.toDual_distribOn (h : DistribOn x y z) :
    DistribOn (toDual x) (toDual y) (toDual z) := by
  have aux : ∀ {a b c : α}, DistribOn a b c →
      DistribOn (toDual c) (toDual a) (toDual b) := fun {a b c} h' ↦ by
    rw [distribOn_iff_sup_inf, sup_comm, sup_comm (toDual c), sup_comm (toDual c)]
    exact congr_arg toDual (DistribOn.inf_sup_right h')
  apply aux
  rw [distribOn_iff_sup_inf, sup_comm y, sup_comm y, sup_comm y]
  exact congr_arg ofDual (aux h).inf_sup_right

@[simp] theorem distribOn_toDual_iff :
    DistribOn (toDual x) (toDual y) (toDual z) ↔ DistribOn x y z :=
  ⟨DistribOn.toDual_distribOn, DistribOn.toDual_distribOn⟩

@[simp] theorem distribOn_ofDual_iff {x y z : αᵒᵈ} :
    DistribOn (ofDual x) (ofDual y) (ofDual z) ↔ DistribOn x y z :=
  distribOn_toDual_iff

theorem distribOn_of_inf_sup_le (h : x ⊓ (y ⊔ z) ≤ x ⊓ y ⊔ x ⊓ z) : DistribOn x y z := by
  replace h := h.antisymm (sup_le (inf_le_inf_left _ le_sup_left) (inf_le_inf_left _ le_sup_right))
  rwa [← distribOn_toDual_iff]

theorem DistribOn.rotate (h : DistribOn x y z) : DistribOn z x y := by
  replace h := h.inf_sup_right
  rw [inf_comm, inf_comm x, inf_comm y] at h
  exact distribOn_of_inf_sup_le h.le

theorem DistribOn.rotate' (h : DistribOn x y z) : DistribOn y z x :=
  h.rotate.rotate

theorem DistribOn.symm_left (h : DistribOn x y z) : DistribOn y x z :=
  h.symm_right.rotate

theorem DistribOn.sup_inf_right (h : DistribOn x y z) : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z) := by
  rw [sup_comm, h.rotate.sup_inf_left, sup_comm, sup_comm z]

theorem DistribOn.inf_sup_left (h : DistribOn x y z) : x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z) := by
  rw [inf_comm, h.rotate'.inf_sup_right, inf_comm, inf_comm z]

theorem distribOn_iff_inf_sup : DistribOn x y z ↔ x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z) :=
  ⟨DistribOn.inf_sup_left, fun h ↦ distribOn_of_inf_sup_le h.le⟩

theorem distribOn_of_le (hxy : x ≤ y) (z : α) : DistribOn x y z :=
  distribOn_of_sup_inf_sup_le <|
    by rw [sup_of_le_right hxy, inf_comm, sup_inf_assoc_of_le _ hxy, inf_comm z]

theorem distribOn_of_sup_inf_le (h : x ⊓ (y ⊔ z) ≤ z) : DistribOn x y z :=
  distribOn_toDual_iff.1 <| distribOn_of_le_sup_inf h

end distrib
section Complements

variable [IsModularLattice α]

theorem exists_rel_complement [BoundedOrder α] [ComplementedLattice α] (hax : a ≤ x) (hxb : x ≤ b) :
    ∃ y, x ⊓ y = a ∧ x ⊔ y = b := by
  set a' : Set.Iic b := ⟨a, hax.trans hxb⟩
  set x' : Set.Ici a' := ⟨⟨x,hxb⟩, hax⟩
  obtain ⟨⟨⟨y,hyb : y ≤ b⟩, hya⟩, hy1, hy2⟩ := exists_isCompl x'
  rw [disjoint_iff, ← Subtype.coe_inj, ← Subtype.coe_inj] at hy1
  rw [codisjoint_iff, ← Subtype.coe_inj, ← Subtype.coe_inj] at hy2
  exact ⟨y, hy1, hy2⟩

end Complements
