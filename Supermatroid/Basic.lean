import LatticeMatroid.ModularLattice
import LatticeMatroid.Continuous

open OrderDual Set

variable {α : Type*} {a b c x y z i j s t : α}
section StrongRefinement

variable [Preorder α] {r : α → α → Prop}

/-- A relation `r` is a `StrongRefinement` (of `≤`) if `r a b → a ≤ b`, and for all `a ≤ b ≤ c`,
  the statements `r a c` and `(r a b ∧ r b c)` are equivalent. This is what we require of the
  'span' and 'cospan' relations in a `Supermatroid`. -/
def StrongRefinement (α : Type*) [Preorder α] (r : α → α → Prop) :=
  (∀ ⦃a b⦄, r a b → a ≤ b) ∧ (∀ ⦃a b c⦄, a ≤ b → b ≤ c → (r a c ↔ (r a b ∧ r b c)))

lemma StrongRefinement.le_of (h : StrongRefinement α r) (hab : r a b) : a ≤ b :=
  h.1 hab

lemma StrongRefinement.trans_of (h : StrongRefinement α r) (hab : r a b) (hbc : r b c) : r a c :=
  (h.2 (h.le_of hab) (h.le_of hbc)).2 ⟨hab, hbc⟩

lemma StrongRefinement.trans_iff (h : StrongRefinement α r) (hab : a ≤ b) (hbc : b ≤ c) :
    r a c ↔ (r a b ∧ r b c) :=
  h.2 hab hbc

lemma StrongRefinement.rel_right_of_rel (h : StrongRefinement α r) (hac : r a c) (hab : a ≤ b)
    (hbc : b ≤ c) : r b c :=
  ((h.2 hab hbc).1 hac).2

lemma StrongRefinement.rel_left_of_rel (h : StrongRefinement α r) (hac : r a c) (hab : a ≤ b)
    (hbc : b ≤ c) : r a b :=
  ((h.2 hab hbc).1 hac).1

lemma StrongRefinement.rel_left_right_of_rel (h : StrongRefinement α r) (hac : r a c) (hax : a ≤ x)
    (hxy : x ≤ y) (hyc : y ≤ c) : r x y :=
  h.rel_left_of_rel (h.rel_right_of_rel hac hax (hxy.trans hyc)) hxy hyc

lemma StrongRefinement.strongRefinement_dual (h : StrongRefinement α r) :
    StrongRefinement αᵒᵈ (fun a b ↦ r (ofDual b) (ofDual a)) := by
  refine ⟨fun a b h' ↦ h.le_of h', fun a b c hab hbc ↦ ?_⟩
  rw [and_comm]
  exact h.2 hbc hab

lemma strongRefinement_dual_iff :
    StrongRefinement α r ↔ StrongRefinement αᵒᵈ (fun a b ↦ r (ofDual b) (ofDual a)) :=
  ⟨StrongRefinement.strongRefinement_dual, StrongRefinement.strongRefinement_dual⟩

lemma StrongRefinement.strongRefinement_ofDual {r : αᵒᵈ → αᵒᵈ → Prop} (hr : StrongRefinement α r) :
    StrongRefinement αᵒᵈ (fun a b ↦ r (toDual b) (toDual a)) := by
  rw [strongRefinement_dual_iff] at hr
  exact hr

lemma StrongRefinement.subtype_strongRefinement (h : StrongRefinement α r) (S : Set α) :
    StrongRefinement S (fun x y ↦ r x y) :=
  ⟨fun _ _ ↦ h.le_of, fun _ _ _ ↦ h.trans_iff⟩

end StrongRefinement

/-- A `Supermatroid` on an ordering is a pair of relations `≤₀` and `≤₁` satisfying axioms
  that make them behave like span and cospan in a matroid. -/
class Supermatroid (α : Type*) [Lattice α] where
  /-- The relation of spanning from below, denoted `a ≤₀ b`. -/
  (SpansLE : α → α → Prop)
  /-- The relation of cospanning from below, denoted `a ≤₁ b`. -/
  (CospansLE : α → α → Prop)
  /-- `≤₀` implies `≤`, and `a ≤₀ b ≤₀ c ↔ a ≤₀ c` for all `b ∈ [a,c]`. -/
  (spansLE_refinement : StrongRefinement α SpansLE)
  /-- `≤₁` implies `≤`, and `a ≤₁ b ≤₁ c ↔ a ≤₁ c` for all `b ∈ [a,c]`. -/
  (cospansLE_refinement : StrongRefinement α CospansLE)
  /-- Every nonempty interval `[a,b]` contains some `x` with `a ≤₁ x ≤₀ b`. -/
  (exists_rel_isBase : ∀ ⦃a b⦄, a ≤ b → ∃ x, CospansLE a x ∧ SpansLE x b)
  /-- There are no diamonds with spans below and cospans above -/
  (eq_of_diamond : ∀ ⦃a b⦄, SpansLE (a ⊓ b) a → SpansLE (a ⊓ b) b →
    CospansLE a (a ⊔ b) → CospansLE b (a ⊔ b) → a = b)
  /-- Some element is cospanned by everything below it. Only needed in unbounded lattices. -/
  (exists_indep' : ∃ i, ∀ x < i, CospansLE x i)
  /-- Some element spans everything above it. Only needed in unbounded lattices. -/
  (exists_spanning' : ∃ s, ∀ x > s, SpansLE s x)

namespace Supermatroid

section Lattice

variable [Lattice α] [Supermatroid α]

infix:50 " ≤₀ " => SpansLE
infix:50 " ≤₁ " => CospansLE

/-- In a `BoundedOrder`, we don't need the `exists_indep'` or `exists_spanning'` axioms. -/
@[simps, reducible]
protected def ofBoundedOrder (α : Type*) [Lattice α] [BoundedOrder α]
    (SpansLE : α → α → Prop)
    (CospansLE : α → α → Prop)
    (spansLE_refinement : StrongRefinement α SpansLE)
    (cospansLE_refinement : StrongRefinement α CospansLE)
    (exists_rel_base : ∀ ⦃a b⦄, a ≤ b → ∃ x, CospansLE a x ∧ SpansLE x b)
    (eq_of_diamond : ∀ ⦃a b⦄, SpansLE (a ⊓ b) a → SpansLE (a ⊓ b) b →
      CospansLE a (a ⊔ b) → CospansLE b (a ⊔ b) → a = b) : Supermatroid α where
  SpansLE := SpansLE
  CospansLE := CospansLE
  spansLE_refinement := spansLE_refinement
  cospansLE_refinement := cospansLE_refinement
  exists_rel_isBase := exists_rel_base
  eq_of_diamond := eq_of_diamond
  exists_indep' := ⟨⊥, by simp⟩
  exists_spanning' := ⟨⊤, by simp⟩

instance : Supermatroid αᵒᵈ where
  SpansLE x y := ofDual y ≤₁ ofDual x
  CospansLE x y := ofDual y ≤₀ ofDual x
  spansLE_refinement := Supermatroid.cospansLE_refinement.strongRefinement_dual
  cospansLE_refinement := Supermatroid.spansLE_refinement.strongRefinement_dual
  exists_rel_isBase _ _ h :=
    let ⟨x, hx⟩ := Supermatroid.exists_rel_isBase (ofDual_le_ofDual.2 h)
    ⟨toDual x, hx.2, hx.1⟩
  eq_of_diamond _ _ hau hbu hia hib := eq_of_diamond (α := α) hia hib hau hbu
  exists_indep' := Supermatroid.exists_spanning' (α := α)
  exists_spanning' := Supermatroid.exists_indep' (α := α)

lemma SpansLE.le (h : x ≤₀ y) : x ≤ y :=
  Supermatroid.spansLE_refinement.le_of h

lemma CospansLE.le (h : x ≤₁ y) : x ≤ y :=
  Supermatroid.cospansLE_refinement.le_of h

@[gcongr]
lemma SpansLE.trans (hxy : x ≤₀ y) (hyz : y ≤₀ z) : x ≤₀ z :=
  Supermatroid.spansLE_refinement.trans_of hxy hyz

lemma SpansLE.mono_right (hxz : x ≤₀ z) (hxy : x ≤ y) (hyz : y ≤ z) : x ≤₀ y :=
  Supermatroid.spansLE_refinement.rel_left_of_rel hxz hxy hyz

lemma SpansLE.mono_left (hxz : x ≤₀ z) (hxy : x ≤ y) (hyz : y ≤ z) : y ≤₀ z :=
  Supermatroid.spansLE_refinement.rel_right_of_rel hxz hxy hyz

lemma SpansLE.mono {x' z' : α} (hxz : x ≤₀ z) (hx : x ≤ x') (hz : z' ≤ z) (h : x' ≤ z') :
    x' ≤₀ z' :=
  (hxz.mono_left hx (h.trans hz)).mono_right h hz

@[gcongr]
lemma CospansLE.trans (hxy : x ≤₁ y) (hyz : y ≤₁ z) : x ≤₁ z := by
  exact Supermatroid.cospansLE_refinement.trans_of hxy hyz

lemma CospansLE.mono_right (hxz : x ≤₁ z) (hxy : x ≤ y) (hyz : y ≤ z) : x ≤₁ y :=
  Supermatroid.cospansLE_refinement.rel_left_of_rel hxz hxy hyz

lemma CospansLE.mono_left (hxz : x ≤₁ z) (hxy : x ≤ y) (hyz : y ≤ z) : y ≤₁ z :=
  Supermatroid.cospansLE_refinement.rel_right_of_rel hxz hxy hyz

lemma CospansLE.mono {x' z' : α} (hxz : x ≤₁ z) (hx : x ≤ x') (hz : z' ≤ z) (h : x' ≤ z') :
    x' ≤₁ z' :=
  (hxz.mono_left hx (h.trans hz)).mono_right h hz

lemma eq_of_infs_span_of_cospan_sups (hix : x ⊓ y ≤₀ x) (hiy : x ⊓ y ≤₀ y) (hxu : x ≤₁ x ⊔ y)
    (hyu : y ≤₁ x ⊔ y) : x = y :=
  eq_of_diamond hix hiy hxu hyu

lemma eq_of_spansLE_spansLE_cospansLE_cospansLE
    (hax : a ≤₀ x) (hay : a ≤₀ y) (hxb : x ≤₁ b) (hyb : y ≤₁ b) : x = y :=
  eq_of_infs_span_of_cospan_sups
    (hax.mono_left (le_inf hax.le hay.le) inf_le_left)
    (hay.mono_left (le_inf hax.le hay.le) inf_le_right)
    (hxb.mono_right le_sup_left (sup_le hxb.le hyb.le))
    (hyb.mono_right le_sup_right (sup_le hxb.le hyb.le))

lemma exists_cospansLE_spansLE_of_le {d} (hcd : c ≤ d) : ∃ (x : α), c ≤₁ x ∧ x ≤₀ d :=
  Supermatroid.exists_rel_isBase hcd

lemma SpansLE.refl {x : α} : x ≤₀ x := by
  obtain ⟨y, hxy, hyx⟩ := exists_cospansLE_spansLE_of_le (c := x) rfl.le
  rwa [← hxy.le.antisymm hyx.le] at hyx

@[refl]
lemma CospansLE.refl : x ≤₁ x :=
  SpansLE.refl (α := αᵒᵈ)

lemma SpansLE.eq_of_cospansLE (h : x ≤₀ y) (h' : x ≤₁ y) : x = y :=
  eq_of_spansLE_spansLE_cospansLE_cospansLE SpansLE.refl h h' CospansLE.refl

lemma CospansLE.eq_of_spansLE (h : x ≤₁ y) (h' : x ≤₀ y) : x = y :=
  h'.eq_of_cospansLE h

@[simp] lemma dual_spansLE_iff {x y : αᵒᵈ} : x ≤₀ y ↔ (ofDual y) ≤₁ (ofDual x) := Iff.rfl

@[simp] lemma dual_cospansLE_iff {x y : αᵒᵈ} : x ≤₁ y ↔ (ofDual y) ≤₀ (ofDual x) := Iff.rfl

@[simp] lemma toDual_spansLE_iff : toDual x ≤₀ toDual y ↔ y ≤₁ x := Iff.rfl

@[simp] lemma toDual_cospansLE_iff : toDual x ≤₁ toDual y ↔ y ≤₀ x := Iff.rfl

lemma SpansLE.toDual_cospansLE (h : x ≤₀ y) : toDual y ≤₁ toDual x :=
  h
lemma CospansLE.toDual_spansLE (h : x ≤₁ y) : toDual y ≤₀ toDual x :=
  h

/-- `x ≤₁ y` iff the only `z` with `x ≤ z ≤₀ y` is `y` itself. -/
lemma cospansLE_iff (hxy : x ≤ y) : (x ≤₁ y) ↔ ∀ z, x ≤ z → z ≤₀ y → z = y := by
  refine ⟨fun h z hxz hzy ↦ hzy.eq_of_cospansLE (h.mono_left hxz hzy.le), fun h ↦ ?_⟩
  obtain ⟨w, hxw, hwy⟩ := exists_cospansLE_spansLE_of_le hxy
  rwa [← h w hxw.le hwy]

/-- `x ≤₀ y` if the only `z` with `x ≤₁ z ≤ y` is `x` itself. -/
lemma spansLE_iff (hxy : x ≤ y) : x ≤₀ y ↔ ∀ z, x ≤₁ z → z ≤ y → x = z := by
  refine ⟨fun h z hxz hzy ↦ hxz.eq_of_spansLE (h.mono_right hxz.le hzy), fun h ↦ ?_⟩
  obtain ⟨w, hxw, hwy⟩ := exists_cospansLE_spansLE_of_le hxy
  rwa [h w hxw hwy.le]

lemma SpansLE.eq_inf_of_cospansLE (hxy : x ≤₀ y) (hxz : x ≤₁ z) : x = y ⊓ z :=
  (hxy.mono_right (le_inf hxy.le hxz.le) inf_le_left).eq_of_cospansLE
    <| hxz.mono_right (le_inf hxy.le hxz.le) inf_le_right

lemma CospansLE.eq_inf_of_spansLE (hxy : x ≤₁ y) (hxz : x ≤₀ z) : x = y ⊓ z := by
  rw [inf_comm]; exact hxz.eq_inf_of_cospansLE hxy

lemma SpansLE.eq_sup_of_cospansLE (hxz : x ≤₀ z) (hyz : y ≤₁ z) : z = x ⊔ y :=
  hxz.toDual_cospansLE.eq_inf_of_spansLE hyz.toDual_spansLE

lemma CospansLE.eq_sup_of_spansLE (hxz : x ≤₁ z) (hyz : y ≤₀ z) : z = x ⊔ y := by
  rw [sup_comm]; exact hyz.eq_sup_of_cospansLE hxz

section IsModularLattice

variable [IsModularLattice α]

lemma CospansLE.spansLE_sup_of_spansLE (hxy : x ≤₁ y) (hxz : x ≤₀ z) : y ≤₀ y ⊔ z := by
  -- Take a base `v` of `[y, y ⊔ z]`
  obtain ⟨v, hyv, hvyz⟩ := exists_cospansLE_spansLE_of_le (show y ≤ y ⊔ z from le_sup_left)
  -- `x` spans and cospans `v ⊓ z`, so they are equal.
  have hxvz : x ≤ v ⊓ z := le_inf (hxy.le.trans hyv.le) hxz.le
  obtain rfl := (hxz.mono_right hxvz inf_le_right).eq_of_cospansLE
    ((hxy.trans hyv).mono_right hxvz inf_le_left)
  convert hvyz
  refine eq_of_le_of_inf_le_of_sup_le hyv.le (z := v ⊓ z) (by simpa [← inf_assoc] using hxy.le) ?_
  rw [sup_comm y, inf_sup_assoc_of_le _ hyv.le, sup_comm z]
  simp [hvyz.le]

lemma SpansLE.spansLE_sup_of_cospansLE (hxy : x ≤₀ y) (hxz : x ≤₁ z) : z ≤₀ y ⊔ z := by
  rw [sup_comm]; exact hxz.spansLE_sup_of_spansLE hxy

lemma CospansLE.inf_cospansLE_of_spansLE (hxz : x ≤₁ z) (hyz : y ≤₀ z) : x ⊓ y ≤₁ y :=
  hxz.toDual_spansLE.spansLE_sup_of_cospansLE hyz.toDual_cospansLE

lemma SpansLE.inf_cospansLE_of_cospansLE (hxz : x ≤₀ z) (hyz : y ≤₁ z) : x ⊓ y ≤₁ x := by
  rw [inf_comm]; exact hyz.inf_cospansLE_of_spansLE hxz

lemma SpansLE.sup (hab : a ≤₀ b) (hac : a ≤₀ c) : a ≤₀ b ⊔ c := by
  -- take a base `x` for `[b,b ⊔ c]` and a base `y` for `[c ⊓ x, x]`.
  obtain ⟨x, hbx, hxu⟩ := exists_cospansLE_spansLE_of_le (show b ≤ b ⊔ c from le_sup_left)
  obtain ⟨y, hcxy, hyx⟩ := exists_cospansLE_spansLE_of_le (show c ⊓ x ≤ x from inf_le_right)
  -- Since `y ≤₀ x` and `b ≤₁ x`, we have `b ⊓ y ≤₁ y`
  have hyb : b ⊓ y ≤₁ y := inf_comm y b ▸ hyx.inf_cospansLE_of_cospansLE hbx
  -- Since `b ≤ x` and `x ⊓ c ≤₁ y`, we have `b ⊓ c ≤ x ⊓ c ≤ y.`
  have hbcy : b ⊓ c ≤ y := (inf_le_inf_right _ hbx.le).trans (inf_comm x c ▸ hcxy.le)
  -- it follows that `b ⊓ y` and `c ⊓ x` both cospan `y` and are spanned by `a`, so are equal
  -- by the diamond axiom.
  have h1 : b ⊓ y = c ⊓ x := eq_of_spansLE_spansLE_cospansLE_cospansLE
    (hab.mono (le_inf hab.le hac.le) inf_le_left (le_inf inf_le_left hbcy))
    (hac.mono (le_inf hab.le hac.le) inf_le_left (le_inf inf_le_right (inf_le_left.trans hbx.le)))
    hyb hcxy
  refine (hab.trans ?_).trans hxu
  simpa [eq_of_le_of_inf_le_of_le_sup hbx.le (by simp [inf_comm, ← h1]) hxu.le] using SpansLE.refl

lemma SpansLE.sup_right (h : x ≤₀ y) (z : α) : x ⊔ z ≤₀ y ⊔ z := by
  obtain ⟨v, hyv, hvyz⟩ := exists_cospansLE_spansLE_of_le (le_sup_left : x ≤ x ⊔ z)
  refine ((hyv.spansLE_sup_of_spansLE h).sup hvyz).mono hvyz.le ?_ (sup_le_sup_right h.le z)
  exact sup_le (le_sup_of_le_left le_sup_right) (le_sup_of_le_right le_sup_right)

lemma SpansLE.sup_left (h : x ≤₀ y) (z : α) : z ⊔ x ≤₀ z ⊔ y := by
  rw [sup_comm, sup_comm z]
  exact h.sup_right z

lemma SpansLE.sup_spansLE_sup {x' y' : α} (h : x ≤₀ y) (h' : x' ≤₀ y') : x ⊔ x' ≤₀ y ⊔ y' :=
  (h.sup_right x').trans (h'.sup_left y)

lemma CospansLE.inf (hxz : x ≤₁ z) (hyz : y ≤₁ z) : x ⊓ y ≤₁ z :=
  SpansLE.sup (α := αᵒᵈ) hxz hyz

end IsModularLattice

section Spans

/-- We say that `x Spans y`, writing `x ⇒₀ y`, if `x ≤₀ y ⊔ x`.
  This is the intuitive notion of spanning without the requirement that `x ≤ y`. -/
def Spans (x y : α) := x ≤₀ y ⊔ x

infix:50 " ⇒₀ " => Spans

lemma spans_iff_spansLE_sup_left : x ⇒₀ y ↔ x ≤₀ y ⊔ x := Iff.rfl

lemma spans_iff_spansLE_sup_right : x ⇒₀ y ↔ x ≤₀ x ⊔ y := by
  rw [sup_comm, spans_iff_spansLE_sup_left]

lemma SpansLE.spans (h : x ≤₀ y) : x ⇒₀ y := by
  rwa [← sup_of_le_left h.le] at h

lemma Spans.refl : x ⇒₀ x := by
  rw [spans_iff_spansLE_sup_left, sup_idem]; exact SpansLE.refl

lemma spansLE_iff_spans_le : x ≤₀ y ↔ (x ≤ y) ∧ x ⇒₀ y :=
  ⟨fun h ↦ ⟨h.le, h.spans⟩,
    fun ⟨hle, h⟩ ↦ by rwa [spans_iff_spansLE_sup_left, sup_of_le_left hle] at h⟩

lemma Spans.spansLE_of_le (h : x ⇒₀ y) (hxy : x ≤ y) : x ≤₀ y :=
  spansLE_iff_spans_le.2 ⟨hxy, h⟩

lemma Spans.mono_right (h : x ⇒₀ y) (hzy : z ≤ y) : x ⇒₀ z := by
  rw [spans_iff_spansLE_sup_right] at h ⊢
  exact h.mono_right le_sup_left <| sup_le_sup_left hzy _

lemma spans_of_ge (h : y ≤ x) : x ⇒₀ y :=
  Spans.refl.mono_right h

variable [IsModularLattice α]

lemma Spans.mono_left (h : x ⇒₀ y) (hxz : x ≤ z) : z ⇒₀ y := by
  rw [spans_iff_spansLE_sup_right] at h ⊢
  have h' := h.sup_left z
  rwa [← sup_assoc, sup_of_le_left hxz] at h'

lemma Spans.mono (h : x ⇒₀ y) (hxx' : x ≤ x') (hy'y : y' ≤ y) : x' ⇒₀ y' :=
  (h.mono_left hxx').mono_right hy'y

lemma Spans.trans (hxy : x ⇒₀ y) (hyz : y ⇒₀ z) : x ⇒₀ z := by
  rw [spans_iff_spansLE_sup_right] at hxy hyz ⊢
  exact (hxy.trans (hyz.sup_left x)).mono_right le_sup_left (sup_le_sup_left le_sup_right _)

lemma Spans.sup (hxy : x ⇒₀ y) (hxz : x ⇒₀ z) : x ⇒₀ (y ⊔ z) := by
  rw [spans_iff_spansLE_sup_left] at hxz hxy ⊢
  have h := hxy.sup hxz
  rwa [← sup_sup_distrib_right] at h

lemma Spans.sup_spans_sup (hxy : x ⇒₀ y) (hwz : w ⇒₀ z) : x ⊔ w ⇒₀ y ⊔ z :=
  (hxy.mono_left le_sup_left).sup (hwz.mono_left le_sup_right)

end Spans

section Cospans

/-- We say that `x Cospans y`, writing `x ⇒₁ y`, if `x ⊓ y ≤ y`.
  This is (definitionally) the dual notion of `Spans`. -/
def Cospans (x y : α) := x ⊓ y ≤₁ y

infix:50 " ⇒₁ " => Cospans

lemma cospans_iff_inf_cospansLE_right : x ⇒₁ y ↔ x ⊓ y ≤₁ y := Iff.rfl

lemma cospans_iff_inf_cospansLE_left : x ⇒₁ y ↔ y ⊓ x ≤₁ y := by
  rw [inf_comm, cospans_iff_inf_cospansLE_right]

lemma Cospans.refl : x ⇒₁ x :=
  Spans.refl (α := αᵒᵈ)

@[simp] lemma dual_spans_iff {x y : αᵒᵈ} : x ⇒₀ y ↔ (ofDual y) ⇒₁ (ofDual x) := Iff.rfl

@[simp] lemma dual_cospans_iff {x y : αᵒᵈ} : x ⇒₁ y ↔ (ofDual y) ⇒₀ (ofDual x) := Iff.rfl

@[simp] lemma toDual_spans_iff : toDual x ⇒₀ toDual y ↔ y ⇒₁ x := Iff.rfl

@[simp] lemma toDual_cospans_iff : toDual x ⇒₁ toDual y ↔ y ⇒₀ x := Iff.rfl

lemma Cospans.toDual_spans (h : x ⇒₁ y) : toDual y ⇒₀ toDual x :=
  h

lemma Spans.toDual_cospans (h : x ⇒₀ y) : toDual y ⇒₁ toDual x :=
  h

lemma cospansLE_iff_cospans_le : x ≤₁ y ↔ (x ≤ y) ∧ x ⇒₁ y :=
  spansLE_iff_spans_le (α := αᵒᵈ)

lemma Cospans.cospansLE_of_le (h : x ⇒₁ y) (hxy : x ≤ y) : x ≤₁ y :=
  cospansLE_iff_cospans_le.2 ⟨hxy,h⟩

lemma Cospans.mono_left (h : x ⇒₁ y) (hxz : x ≤ z) : z ⇒₁ y :=
  h.toDual_spans.mono_right hxz

variable [IsModularLattice α]

lemma Cospans.mono_right (h : x ⇒₁ y) (hzy : z ≤ y) : x ⇒₁ z :=
  h.toDual_spans.mono_left hzy

lemma Cospans.mono (h : x ⇒₁ y) (hxx' : x ≤ x') (hy'y : y' ≤ y) : x' ⇒₁ y' :=
  (h.mono_left hxx').mono_right hy'y

lemma cospans_of_ge (h : y ≤ x) : x ⇒₁ y :=
  Cospans.refl.mono_right h

lemma Cospans.trans (hxy : x ⇒₁ y) (hyz : y ⇒₁ z) : x ⇒₁ z :=
  hyz.toDual_spans.trans hxy.toDual_spans

lemma Cospans.inf (hxz : x ⇒₁ z) (hyz : y ⇒₁ z) : x ⊓ y ⇒₁ z :=
  hxz.toDual_spans.sup hyz.toDual_spans

lemma Cospans.inf_cospans_inf (hxy : x ⇒₁ y) (hwz : w ⇒₁ z) : x ⊓ w ⇒₁ y ⊓ z :=
  (hxy.mono_right inf_le_left).inf (hwz.mono_right inf_le_right)

end Cospans


end Lattice

section CompleteLattice

variable [CompleteLattice α] [Supermatroid α] {C : Set α} {κ : Sort*}

section closure

/-- The unique maximal element spanned by `x`. -/
def closure (x : α) := sSup {y | x ≤₀ y}

variable [JoinContinuous α] [IsModularLattice α]

lemma spansLE_closure (x : α) : x ≤₀ closure x := by
  have hmax := zorn_le_nonempty₀ {y | x ≤₀ y} ?_ x SpansLE.refl
  · obtain ⟨m, hxm, hm : Maximal (x ≤₀ ·) m⟩ := hmax
    have hle : m ≤ closure x := le_sSup hm.1
    have hle' : closure x ≤ m := by
      refine sSup_le (fun y (hy : x ≤₀ y) ↦ ?_)
      grw [hm.eq_of_le (y := m ⊔ y) (hm.1.sup hy) le_sup_left, ← le_sup_right]
    grw [hle'.antisymm hle, hm.prop]
    exact SpansLE.refl
  refine fun C hxC hC y hyC ↦ ⟨sSup C, ?_, fun z hz ↦ le_sSup hz⟩
  obtain ⟨z, hxz, hzs⟩ := exists_cospansLE_spansLE_of_le <| (hxC hyC).le.trans (le_sSup hyC)
  have h := fun y (hy : y ∈ C) ↦
    ((hxz.mono_right (le_inf  hxz.le (hxC hy).le) inf_le_left).eq_of_spansLE
    <| (hxC hy).mono_right (le_inf hxz.le (hxC hy).le) inf_le_right).symm
  have hdist := JoinContinuous.inf_distrib_sSup z hC.directedOn
  rw [sSup_eq_iSup, biSup_congr h, biSup_const ⟨y, hyC⟩, ← sSup_eq_iSup,
    inf_of_le_left hzs.le] at hdist
  rwa [mem_setOf, ← hdist]

lemma le_closure_iff_spans : y ≤ closure x ↔ x ⇒₀ y :=
  ⟨(spansLE_closure x).spans.mono_right, fun h ↦ le_sup_left.trans (le_sSup h)⟩

lemma le_closure_self (x : α) : x ≤ closure x :=
  le_closure_iff_spans.2 Spans.refl

@[simp] lemma closure_closure : closure (closure x) = closure x := by
  rw [le_antisymm_iff, le_closure_iff_spans, and_iff_left (le_closure_self _)]
  exact ((spansLE_closure x).trans (spansLE_closure _)).spans

lemma Spans.spans_closure (h : x ⇒₀ y) : x ⇒₀ closure y :=
  h.trans (spansLE_closure y).spans

@[simp] lemma closure_le_closure_iff_spans : closure y ≤ closure x ↔ x ⇒₀ y := by
  rw [le_closure_iff_spans]
  exact ⟨fun h ↦ h.mono_right (le_closure_self y), fun h ↦ h.spans_closure⟩

/-- The unique minimal element cospanning `x`. -/
def coclosure (x : α) := sInf {y | y ≤₁ x}

omit [JoinContinuous α] in
lemma coclosure_cospansLE [MeetContinuous α] (x : α) : coclosure x ≤₁ x :=
  spansLE_closure (toDual x)

omit [JoinContinuous α] in
lemma coclosure_le_iff_cospans [MeetContinuous α] : (coclosure x ≤ y) ↔ y ⇒₁ x :=
  le_closure_iff_spans (α := αᵒᵈ)

end closure

section SupInf

variable {κ : Type*} {y : κ → α} {K : Set κ} {S : Set α} [IsModularLattice α] [JoinContinuous α]

lemma spansLE_iSup [Nonempty κ] (h : ∀ k, x ≤₀ y k) : x ≤₀ ⨆ (k : κ), y k := by
  rw [spansLE_iff_spans_le, ← le_closure_iff_spans, iSup_le_iff]
  exact ⟨(h (Classical.arbitrary κ)).le.trans <| le_iSup y _ ,
    fun k ↦ le_closure_iff_spans.2 (h k).spans⟩

lemma spans_iSup (h : ∀ k, x ⇒₀ y k) : x ⇒₀ ⨆ k, y k := by
  simp_rw [← le_closure_iff_spans] at h ⊢
  exact iSup_le h

lemma spansLE_biSup (hK : K.Nonempty) (h : ∀ k ∈ K, x ≤₀ y k) :
    x ≤₀ ⨆ (k ∈ K), y k := by
  rw [← iSup_subtype'']
  have := hK.to_subtype
  exact spansLE_iSup (by simpa)

lemma spans_biSup (h : ∀ k ∈ K, x ⇒₀ y k) : x ⇒₀ ⨆ k ∈ K, y k := by
  rw [← le_closure_iff_spans]
  simp only [iSup_le_iff]
  simp_rw [le_closure_iff_spans]
  assumption

lemma spansLE_sSup (hS : S.Nonempty) (hxS : ∀ y ∈ S, x ≤₀ y) : x ≤₀ sSup S := by
  rw [sSup_eq_iSup]
  exact spansLE_biSup hS hxS

lemma spans_sSup (hxS : ∀ y ∈ S, x ⇒₀ y) : x ⇒₀ sSup S := by
  rw [sSup_eq_iSup]
  exact spans_biSup hxS

lemma iSup_spans_iSup {x y : κ → α} (h : ∀ k, x k ⇒₀ y k) : ⨆ k, x k ⇒₀ ⨆ k, y k :=
  spans_iSup <| fun k ↦ (h k).mono_left (le_iSup x k)

lemma iSup_spansLE_iSup {x y : κ → α} (h : ∀ k, x k ≤₀ y k) : ⨆ k, x k ≤₀ ⨆ k, y k :=
  (iSup_spans_iSup (fun k ↦ (h k).spans)).spansLE_of_le (iSup_mono fun k ↦ (h k).le)

omit [JoinContinuous α]
variable [MeetContinuous α]

lemma iInf_cospansLE [Nonempty κ] (h : ∀ k, y k ≤₁ x) : ⨅ k, y k ≤₁ x :=
  spansLE_iSup (α := αᵒᵈ) h

lemma iInf_cospans (h : ∀ k, y k ⇒₁ x) : ⨅ k, y k ⇒₁ x :=
  spans_iSup (α := αᵒᵈ) h

lemma sInf_cospansLE (hS : S.Nonempty) (hxS : ∀ y ∈ S, y ≤₁ x) : sInf S ≤₁ x :=
  spansLE_sSup (α := αᵒᵈ) hS hxS

lemma sInf_cospans (hxS : ∀ y ∈ S, y ⇒₁ x) : sInf S ⇒₁ x :=
  spans_sSup (α := αᵒᵈ) hxS

end SupInf

end CompleteLattice

end Supermatroid
