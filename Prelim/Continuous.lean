import Mathlib.Order.CompactlyGenerated.Basic
import Mathlib.Tactic.ApplyFun

open OrderDual Set

section ContinuousGeometry

class JoinContinuous (α : Type*) [CompleteLattice α] : Prop where
  (inf_distrib_sSup : ∀ (x : α) ⦃D : Set α⦄, DirectedOn (· ≤ ·) D → x ⊓ (sSup D) = ⨆ i ∈ D, x ⊓ i)

class MeetContinuous (α : Type*) [CompleteLattice α] : Prop where
  (sup_distrib_sInf : ∀ (x : α) ⦃D : Set α⦄,
    DirectedOn (fun x y ↦ y ≤ x) D → x ⊔ (sInf D) = ⨅ i ∈ D, x ⊔ i)

instance {α : Type*} [CompleteLattice α] [MeetContinuous α] : JoinContinuous αᵒᵈ where
  inf_distrib_sSup x _ h := MeetContinuous.sup_distrib_sInf (ofDual x) h

instance {α : Type*} [CompleteLattice α] [JoinContinuous α] : MeetContinuous αᵒᵈ where
  sup_distrib_sInf x _ h := JoinContinuous.inf_distrib_sSup (ofDual x) h

/-- Von Neumann's continuous geometries, defined as complete complemented modular lattices
  that are meet-continuous and join-continuous. These are the setting on which a continuous
  analogue of dimension makes sense, so are a reasonable place for infinite L-matroids to live. -/
class ContinuousGeometry (α : Type*) extends CompleteLattice α, IsModularLattice α,
  JoinContinuous α, MeetContinuous α, ComplementedLattice α

/-- The dual lattice of a continuous geometry is a continuous geometry. -/
-- Why doesn't `infer_instance` work here?
instance {α : Type*} [ContinuousGeometry α] : ContinuousGeometry αᵒᵈ := ‹_›

instance {α : Type*} [CompleteLattice α] [JoinContinuous α] {a : α} : JoinContinuous (Iic a) where
  inf_distrib_sSup x D hD := by
    rw [← Subtype.val_inj]
    simp only [Iic.coe_inf, Iic.coe_sSup, Iic.coe_iSup]
    rw [JoinContinuous.inf_distrib_sSup, iSup_image]
    exact directedOn_onFun_iff.mp hD

instance {α : Type} [CompleteLattice α] [MeetContinuous α] {a : α} : MeetContinuous (Iic a) where
  sup_distrib_sInf x D hD := by
    obtain (rfl | ⟨y, hy⟩) := eq_empty_or_nonempty D
    · obtain ⟨x, h⟩ := x
      simp
    rw [← Subtype.val_inj, Subtype.coe_sup (fun _ _ ↦ sup_le)]
    convert MeetContinuous.sup_distrib_sInf (x : α) (D := Subtype.val '' D) ?_
    · simp only [Iic.coe_sInf, inf_eq_right]
      grw [sInf_image, biInf_le _ hy, show y ≤ a from y.2]
    · rw [iInf_image, Iic.coe_biInf, inf_of_le_right]
      · rfl
      grw [biInf_le _ hy]
      simp [show x ≤ a from x.2, show y ≤ a from y.2]
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      obtain ⟨z, hz, hxz, hyz⟩ := hD x hx y hy
      refine ⟨z, ⟨z, hz, rfl⟩, hxz, hyz⟩

end ContinuousGeometry
