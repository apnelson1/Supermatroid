import Supermatroid.Prelim.ENat
import Mathlib.Order.KrullDimension

open Order

variable {α β : Type*} {a b x y : α}

section Order

variable [Preorder α] [Preorder β]

lemma Order.height_strictMono' (hxy : x < y) (hy : height y < ⊤) : height x < height y :=
  height_strictMono hxy <| (height_mono hxy.le).trans_lt hy

@[simps]
def LTSEries.map' (p : LTSeries α) (f : α → β)
    (hf : StrictMonoOn f {x | x ∈ p}) : LTSeries β where
      length := p.length
      toFun i := f (p i)
      step i := hf ⟨_, rfl⟩ ⟨_, rfl⟩ <| p.step i

lemma LTSeries.le_last_of_mem (p : LTSeries α) {a : α} (ha : a ∈ p) :
    a ≤ p.last := by
  obtain ⟨y, rfl : p.toFun y = a⟩ := by simpa only [RelSeries.mem_def, Set.mem_range] using ha
  exact p.monotone <| Fin.le_last y

lemma LTSeries.head_le_of_mem (p : LTSeries α) {a : α} (ha : a ∈ p) :
    p.head ≤ a := by
  obtain ⟨y, rfl : p.toFun y = a⟩ := by simpa only [RelSeries.mem_def, Set.mem_range] using ha
  exact p.monotone zero_le

@[simp]
lemma LTSeries.mem_eraseLast {p : LTSeries α} {a : α} (hp : p.length ≠ 0) :
    a ∈ p.eraseLast ↔ a ∈ p ∧ a ≠ p.last := by
  nth_rw 1 [iff_comm, ← p.snoc_self_eraseLast hp, RelSeries.mem_snoc, or_and_right,
    or_iff_left (by simp), and_iff_left_iff_imp]
  rintro ha rfl
  exact (LTSeries.le_last_of_mem _ ha).not_gt <| RelSeries.eraseLast_last_rel_last p hp

lemma height_eq_iSup_covBy_height {x : α} (hx : height x < ⊤) :
    height x = ⨆ y, ⨆ (_ : y ⋖ x), height y + 1 := by
  refine le_antisymm ?_ ?_
  · generalize hu : height x = u
    lift u to ℕ using hu ▸ hx.ne
    obtain ⟨p, hpx, rfl⟩ := exists_series_of_height_eq_coe _ hu
    induction p using RelSeries.inductionOn' generalizing x with
    | singleton x => simp
    | snoc p y hy hp =>
    obtain rfl : y = x := by simpa using hpx
    simp only [RelSeries.snoc_length, Nat.cast_add, Nat.cast_one]
    grw [← le_iSup₂ (i := p.last), ENat.add_one_le_add_one_iff, length_le_height_last]
    by_contra hcon
    rw [not_covBy_iff hy] at hcon
    obtain ⟨c, hpc, hcy⟩ := hcon
    simp only [RelSeries.snoc_length, Nat.cast_add, Nat.cast_one] at hu
    have hcon' := length_le_height_last (p := (p.snoc c hpc).snoc y (by simpa))
    simp [← hu, hx.ne] at hcon'
  simp only [iSup_le_iff]
  exact fun i hix ↦ Order.add_one_le_of_lt <| height_strictMono' hix.lt hx

lemma height_eq_biSup_covBy_height {x : α} (hx : height x < ⊤) :
    height x = ⨆ y ∈ {y | y ⋖ x}, height y + 1 :=
  height_eq_iSup_covBy_height hx

lemma exists_le_covBy_of_height_lt_top (hab : a < b) (hb : height b < ⊤) : ∃ c, a ≤ c ∧ c ⋖ b := by
  by_contra! hcon
  suffices aux : ∀ (k : ℕ), ∃ x, a ≤ x ∧ x < b ∧ k ≤ height x by
    generalize hu : height b = u
    lift u to ℕ using hu ▸ hb.ne
    obtain ⟨x, -, hxb, hh⟩ := aux u
    exact (height_strictMono' hxb hb).not_ge <| hu.trans_le hh
  intro k
  induction k with
  | zero => exact ⟨a, rfl.le, hab, by simp⟩
  | succ k ih =>
    obtain ⟨x, hax, hxb, hkx⟩ := ih
    obtain ⟨y, hy⟩ := (not_covBy_iff hxb).1 <| hcon x hax
    refine ⟨y, hax.trans hy.1.le, hy.2, ?_⟩
    grw [← Order.add_one_le_of_lt (height_strictMono' hy.1 ?_), Nat.cast_add, hkx, Nat.cast_one]
    exact (height_mono hy.2.le).trans_lt hb

lemma exists_le_covBy_of_height_ne_zero_lt_top (ha0 : height a ≠ 0) (hatop : height a < ⊤) :
    ∃ b, b ⋖ a := by
  contrapose! ha0
  simpa [height_eq_iSup_covBy_height hatop]

lemma exists_relSeries_covBy {a : α} (ha : height a < ⊤) :
    ∃ p : RelSeries (fun x ↦ x.1 ⋖ x.2), p.last = a ∧ p.length = height a := by
  have hlt := height_eq_biSup_covBy_height ha ▸ ha
  obtain h0 | halt := eq_zero_or_pos (height a)
  · refine ⟨RelSeries.singleton _ a, by simp [h0]⟩
  obtain ⟨x, hxa : x ⋖ a, hxh : _ = ⨆ i ∈ {i | i ⋖ a}, _⟩ :=
    ENat.exists_eq_biSup_of_lt_top (exists_le_covBy_of_height_ne_zero_lt_top halt.ne.symm ha) _ hlt
  have hxalt : height x < height a := height_strictMono' hxa.lt ha
  obtain ⟨q, rfl, hqh⟩ := exists_relSeries_covBy (hxalt.trans ha)
  refine ⟨q.snoc a hxa, by simp, ?_⟩
  rw [RelSeries.snoc_length, Nat.cast_add, Nat.cast_one, hqh, hxh, height_eq_biSup_covBy_height ha]
termination_by height a

end Order

variable [Lattice α] [IsLowerModularLattice α]

lemma CovBy.height_eq {a b : α} (h : a ⋖ b) : height b = height a + 1 := by
  refine (height_add_one_le h.lt).antisymm' <| height_le_iff'.2 fun p hp ↦ ?_
  rw [← hp] at h
  by_cases hp0 : p.length = 0
  · simp [hp0]
  rw [← p.snoc_self_eraseLast hp0, RelSeries.snoc_length, Nat.cast_add, Nat.cast_one,
      ENat.add_one_le_add_one_iff]
  set z := p.eraseLast.last with hz
  by_cases hle : z ≤ a
  · grw [Order.length_le_height_last, ← hz, height_mono hle]
  obtain hza | hza := h.eq_or_eq (c := z ⊔ a) (by simp) (sup_le
    (p.le_last_of_mem <| by simp [hz, RelSeries.mem_def]) h.le)
  · simp [hle] at hza
  rw [← hza] at h
  have hc' := inf_covBy_of_covBy_sup_right h
  have hzza : z < z ⊔ a := hz ▸ hza ▸ p.eraseLast_last_rel_last hp0
  have hlt : z ⊓ a < a := by simpa [inf_lt_right] using hzza
  obtain htop | hlttop := eq_top_or_lt_top (height (z ⊓ a))
  · grw [← height_mono (show z ⊓ a ≤ a by simp), htop, ← le_top]
  have hlt' := height_strictMono hlt hlttop
  have ih := hc'.height_eq
  grw [← Order.add_one_le_of_lt hlt', ← ih, Order.length_le_height_last]
termination_by height a

lemma RelSeries.height_last_eq_length (p : RelSeries (fun x : α × α ↦ x.1 ⋖ x.2))
    (hp0 : IsMin p.head) : height p.last = p.length := by
  induction p using RelSeries.inductionOn' with
  | singleton x => simpa
  | snoc p x hx hp =>
    rw [snoc_length, Nat.cast_add, ← hp (by simpa using hp0), last_snoc, Nat.cast_one,
      ← hx.height_eq]

lemma RelSeries.height_last_eq (p : RelSeries (fun x : α × α ↦ x.1 ⋖ x.2)) :
    height p.last = height p.head + p.length := by
  induction p using RelSeries.inductionOn' with
  | singleton x => simp
  | snoc p x hx hp =>
    simp only [last_snoc, head_snoc, snoc_length, Nat.cast_add, Nat.cast_one,
      ← add_assoc, ← hp, hx.height_eq]

lemma exists_relSeries_covBy_of_le {b : α} (hab : a ≤ b) (hb : height b < ⊤) :
    ∃ p : RelSeries (fun x ↦ x.1 ⋖ x.2),
      p.head = a ∧ p.last = b ∧ height a + p.length = height b := by
  obtain rfl | hab := hab.eq_or_lt
  · exact ⟨RelSeries.singleton _ a, by simp⟩
  obtain ⟨c, hac, hcb⟩ := exists_le_covBy_of_height_lt_top hab hb
  have hcb' : height c < height b := height_strictMono' hcb.lt hb
  obtain ⟨p, hp, rfl, h⟩ := exists_relSeries_covBy_of_le hac (hcb'.trans hb)
  exact ⟨p.snoc b hcb, by simp [hp, ← add_assoc, h, hcb.height_eq]⟩
termination_by height b

lemma height_inf_add_height_sup {α : Type*} [Lattice α] [IsModularLattice α] (a b : α) :
    height (a ⊓ b) + height (a ⊔ b) = height a + height b := by
  obtain hb | hb := eq_top_or_lt_top (height b)
  · grw [hb, add_top, ← top_le_iff, ← height_mono le_sup_right, hb, add_top]
  by_cases hba : b ≤ a
  · rw [inf_of_le_right hba, sup_of_le_left hba, add_comm]
  rw [← inf_lt_right] at hba
  obtain ⟨b', hab', hb'b⟩ := exists_le_covBy_of_height_lt_top hba hb
  have hhlt : height b' < height b := height_strictMono' hb'b.lt hb
  have hi : b ⊓ (a ⊔ b') = b' := by
    rwa [← inf_sup_assoc_of_le _ hb'b.le, sup_eq_right, inf_comm]
  have hc' := covBy_sup_of_inf_covBy_left <| hi ▸ hb'b
  have heq : a ⊓ b' = a ⊓ b := by
    nth_grw 1 [le_antisymm_iff, hb'b.le, and_iff_right rfl.le, le_inf inf_le_left hab']
  rw [hb'b.height_eq, ← add_assoc, ← height_inf_add_height_sup a b', add_assoc,
    ← hc'.height_eq, sup_comm _ b', ← sup_assoc, sup_of_le_left hb'b.le, sup_comm, heq]
termination_by height b
