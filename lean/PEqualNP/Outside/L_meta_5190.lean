import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership

namespace PEqualNP.Outside.L_meta_5190

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l : List ℕ) (f f' : ℕ → Bool) (h : ∀ i, f i = true → f' i = true) :
    op.eval (l.map f) = true → op.eval (l.map f') = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro H i hi
    exact h i (H i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, H⟩
    exact ⟨i, hi, h i H⟩

theorem foldl_mono (gs : List Gate) (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w w' : List Bool) (hl : w.length = w'.length)
    (hw : ∀ i, w.getD i false = true → w'.getD i false = true) :
    ∀ i, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD
        i false = true →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w').getD
        i false = true := by
  induction gs generalizing w w' with
  | nil => simpa using hw
  | cons g gs ih =>
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
    · simp [hl]
    · intro i hi
      have hb := eval_mono g.op (hg g List.mem_cons_self) g.inputs _ _ hw
      rcases lt_trichotomy i w.length with h | h | h
      · rw [List.getD_append _ _ _ _ h] at hi
        rw [List.getD_append _ _ _ _ (hl ▸ h)]
        exact hw i hi
      · subst h
        rw [List.getD_append_right _ _ _ _ le_rfl] at hi
        rw [hl, List.getD_append_right _ _ _ _ le_rfl]
        simp only [Nat.sub_self, List.getD_cons_zero] at hi ⊢
        exact hb hi
      · rw [List.getD_append_right _ _ _ _ h.le] at hi
        obtain ⟨k, hk⟩ : ∃ k, i - w.length = k + 1 := ⟨i - w.length - 1, by omega⟩
        rw [hk] at hi
        simp at hi

theorem gate_mono (n : ℕ) (C : Circuit) (hC : Monotone2 C) (j : ℕ) (a v : Fin n)
    (h : gateVal n C j (pairInput a a) = true) : gateVal n C j (pairInput a v) = true := by
  unfold gateVal Circuit.wires at *
  refine foldl_mono C.gates ?_ _ _ (by simp) ?_ _ h
  · intro g hg
    have := (hC g hg).1
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this
  · intro i hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hi ⊢
    by_cases hin : i < n
    · simp only [hin, Option.getD_some, List.ofFnNthVal, dite_true] at hi ⊢
      simp only [pairInput, or_self, decide_eq_true_eq] at hi
      simp [pairInput, hi]
    · simp [hin, List.ofFnNthVal] at hi

theorem no_tri {V : Type} (G : SimpleGraph V)
    (hc : ∀ (v : V) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length)
    {a b c : V} (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a) : False := by
  have n1 := hab.ne
  have n2 := hbc.ne
  have n3 := hca.ne
  have hcyc : (SimpleGraph.Walk.cons hab (.cons hbc (.cons hca .nil))).IsCycle := by
    rw [SimpleGraph.Walk.cons_isCycle_iff]
    refine ⟨?_, ?_⟩
    · simp [SimpleGraph.Walk.cons_isPath_iff, n2, n3, n1.symm]
    · simp [Sym2.eq_iff, n1, n2, n3.symm]
  have := hc a _ hcyc
  simp at this

theorem no_sq {V : Type} (G : SimpleGraph V)
    (hc : ∀ (v : V) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length)
    {a b c d : V} (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hbd : b ≠ d) (hac : a ≠ c) : False := by
  have n1 := hab.ne
  have n2 := hbc.ne
  have n3 := hcd.ne
  have n4 := hda.ne
  have hcyc :
      (SimpleGraph.Walk.cons hab (.cons hbc (.cons hcd (.cons hda .nil)))).IsCycle := by
    rw [SimpleGraph.Walk.cons_isCycle_iff]
    refine ⟨?_, ?_⟩
    · simp [SimpleGraph.Walk.cons_isPath_iff, n2, n3, n4, hbd, n1.symm, hac.symm]
    · simp [Sym2.eq_iff, n1, n2, n3, n4, hbd, hac, n1.symm, n4.symm, hbd.symm, hac.symm]
  have := hc a _ hcyc
  simp at this

theorem deg_bound (m : ℕ) (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]
    (hdeg : ∀ v : Fin m, G.degree v = 0 ∨ 3 ≤ G.degree v)
    (hc : ∀ (v : Fin m) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) (a : Fin m) :
    2 * G.degree a + 1 ≤ m := by
  classical
  have ex : ∀ n : Fin m, G.Adj a n → ∃ w, G.Adj n w ∧ w ≠ a := by
    intro n hn
    have hd : 3 ≤ G.degree n := by
      rcases hdeg n with h | h
      · exfalso
        have : 0 < G.degree n :=
          Finset.card_pos.mpr ⟨a, (G.mem_neighborFinset n a).mpr hn.symm⟩
        omega
      · exact h
    have hcard : 0 < ((G.neighborFinset n).erase a).card := by
      have := Finset.pred_card_le_card_erase (s := G.neighborFinset n) (a := a)
      rw [SimpleGraph.card_neighborFinset_eq_degree] at this
      omega
    obtain ⟨w, hw⟩ := Finset.card_pos.mp hcard
    rw [Finset.mem_erase, SimpleGraph.mem_neighborFinset] at hw
    exact ⟨w, hw.2, hw.1⟩
  let W : Fin m → Fin m := fun n => if h : G.Adj a n then Classical.choose (ex n h) else n
  have hW : ∀ n, G.Adj a n → G.Adj n (W n) ∧ W n ≠ a := by
    intro n hn
    simp only [W, hn, dite_true]
    exact Classical.choose_spec (ex n hn)
  let N := G.neighborFinset a
  have hinj : Set.InjOn W N := by
    intro n1 h1 n2 h2 heq
    rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at h1 h2
    by_contra hne
    obtain ⟨e1, f1⟩ := hW n1 h1
    obtain ⟨e2, f2⟩ := hW n2 h2
    rw [heq] at e1
    exact no_sq G hc h1 e1 e2.symm h2.symm hne f2.symm
  have hdisj : Disjoint N (N.image W) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx'
    rw [SimpleGraph.mem_neighborFinset] at hn hx
    obtain ⟨e, _⟩ := hW n hn
    exact no_tri G hc hn e hx.symm
  have hnot : a ∉ N ∪ N.image W := by
    rw [Finset.mem_union, not_or]
    refine ⟨fun h => ((G.mem_neighborFinset a a).mp h).ne rfl, ?_⟩
    intro h
    obtain ⟨n, hn, he⟩ := Finset.mem_image.mp h
    rw [SimpleGraph.mem_neighborFinset] at hn
    exact (hW n hn).2 he
  have hcard : (insert a (N ∪ N.image W)).card = 2 * G.degree a + 1 := by
    rw [Finset.card_insert_of_notMem hnot, Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injOn hinj, SimpleGraph.card_neighborFinset_eq_degree]
    ring
  have := Finset.card_le_univ (insert a (N ∪ N.image W))
  rw [hcard, Fintype.card_fin] at this
  exact this

end PEqualNP.Outside.L_meta_5190

theorem PEqualNP.Outside.L_meta_5190 : ∀ (x1 x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj],   (2 : ℕ) * x1 + (1 : ℕ) ≤ x2 →     (∀ (x6 : Fin x2), x3.degree x6 = (0 : ℕ) ∨ (3 : ℕ) ≤ x3.degree x6) →       (∀ (x7 : Fin x2) (x8 : x3.Walk x7 x7), x8.IsCycle → (5 : ℕ) ≤ x8.length) →         ∀ (x8 : PEqualNP.CircuitLowerBounds.Circuit),           PEqualNP.MetaComplexity.Monotone2 x8 →             ∀ (x10 x11 : Fin x2) (x12 : Fin x8.gates.length),               x3.Adj x10 x11 →                 have x14 : Fin x2 → Fin x2 → Prop := fun (x14 x15 : Fin x2) => PEqualNP.EdgeOwnership.gateVal x2 x8 (↑x12) (PEqualNP.EdgeOwnership.pairInput x14 x15) = Bool.true;                 have x15 : Fin x2 × Fin x2 → Finset (Fin x2) := fun (x15 : Fin x2 × Fin x2) => {x15.1, x15.2} \ {x10, x11};                 x14 x10 x10 ∨ x14 x11 x11 → ∃ (x17 : Finset (Fin x2 × Fin x2)), x17.card = x1 ∧ (∀ x18 ∈ x17, x14 x18.1 x18.2 ∧ ¬x3.Adj x18.1 x18.2) ∧ ∀ x18 ∈ x17, ∀ x20 ∈ x17, x18 ≠ x20 → Disjoint (x15 x18) (x15 x20) := by
  intro x1 x2 G inst hsize hdeg hc C hC x10 x11 j hadj
  intro x14 x15 hstart
  classical
  obtain ⟨a, ha, htrue⟩ : ∃ a, (a = x10 ∨ a = x11) ∧
      gateVal x2 C (↑j) (pairInput a a) = true := by
    rcases hstart with h | h
    · exact ⟨x10, Or.inl rfl, h⟩
    · exact ⟨x11, Or.inr rfl, h⟩
  have hd := PEqualNP.Outside.L_meta_5190.deg_bound x2 G hdeg hc a
  let T := (G.neighborFinset a)ᶜ
  have hT : T.card + G.degree a = x2 := by
    have h1 : T.card = x2 - G.degree a := by
      simp only [T, Finset.card_compl, Fintype.card_fin,
        SimpleGraph.card_neighborFinset_eq_degree]
    omega
  obtain ⟨U, hUT, hUc⟩ := Finset.exists_subset_card_eq (s := T) (n := x1) (by omega)
  refine ⟨U.image (fun v => (a, v)), ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ (fun v w h => (Prod.mk.inj h).2), hUc]
  · intro p hp
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
    have hvT := hUT hv
    simp only [T, Finset.mem_compl, SimpleGraph.mem_neighborFinset] at hvT
    exact ⟨PEqualNP.Outside.L_meta_5190.gate_mono x2 C hC _ a v htrue, hvT⟩
  · intro p hp q hq hpq
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hq
    have hvw : v ≠ w := fun h => hpq (by rw [h])
    rw [Finset.disjoint_left]
    intro z hz hz'
    simp only [x15, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hz hz'
    rcases ha with rfl | rfl
    · rcases hz.1 with h1 | h1
      · exact hz.2 (Or.inl h1)
      · rcases hz'.1 with h2 | h2
        · exact hz'.2 (Or.inl h2)
        · exact hvw (h1 ▸ h2)
    · rcases hz.1 with h1 | h1
      · exact hz.2 (Or.inr h1)
      · rcases hz'.1 with h2 | h2
        · exact hz'.2 (Or.inr h2)
        · exact hvw (h1 ▸ h2)
