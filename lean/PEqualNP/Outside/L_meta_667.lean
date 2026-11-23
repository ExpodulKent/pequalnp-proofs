import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_667_aux

abbrev SupportData667 := ℕ → Finset (Fin 13)
abbrev PairData667 := ℕ → Fin 13 → Fin 13 → Prop

def MonoReq667 (sup : SupportData667) (hit : PairData667) : Prop :=
  ∀ w a b, a ∈ sup w ∨ b ∈ sup w → hit w a b

def StepReq667 (sup : SupportData667) (hit : PairData667) : Prop :=
  ∀ w, 2 ≤ (sup w).card → sup w ≠ Finset.univ →
    ∃ u v, u < w ∧ v < w ∧
      ((sup w = sup u ∪ sup v ∧ ∀ a b, hit w a b ↔ hit u a b ∨ hit v a b) ∨
       (sup w = sup u ∩ sup v ∧ ∀ a b, hit w a b ↔ hit u a b ∧ hit v a b))

def LocalModel :=
  { d : SupportData667 × PairData667 // MonoReq667 d.1 d.2 ∧ StepReq667 d.1 d.2 }

namespace LocalModel

def sup (M : LocalModel) : SupportData667 := M.1.1

def hit (M : LocalModel) : PairData667 := M.1.2

lemma mono (M : LocalModel) : MonoReq667 M.sup M.hit := M.2.1

lemma step (M : LocalModel) : StepReq667 M.sup M.hit := M.2.2

def mk (sup : SupportData667) (hit : PairData667)
    (hmono : MonoReq667 sup hit) (hstep : StepReq667 sup hit) : LocalModel :=
  ⟨(sup, hit), hmono, hstep⟩

def Own (M : LocalModel) (L : Finset (Fin 13)) (w : ℕ) : Prop :=
  M.sup w ⊆ L ∧ 2 ≤ (M.sup w).card

private theorem exOut {D L : Finset (Fin 13)} (hn : ¬ D ⊆ L) :
    ∃ a, a ∈ D ∧ a ∉ L := by
  classical
  by_contra h
  apply hn
  intro x hx
  by_contra hL
  exact h ⟨x, hx, hL⟩

private theorem small_of_proper {D L : Finset (Fin 13)}
    (hL : L ≠ Finset.univ) (hs : D ⊆ L) : D ≠ Finset.univ := by
  intro he
  apply hL
  ext x
  constructor
  · intro _
    exact Finset.mem_univ _
  · intro hx
    apply hs
    rw [he]
    exact hx

private theorem and_subsets {D A B : Finset (Fin 13)} (h : D = A ∩ B) :
    D ⊆ A ∧ D ⊆ B := by
  constructor
  · intro x hx
    rw [h] at hx
    exact (Finset.mem_inter.mp hx).1
  · intro x hx
    rw [h] at hx
    exact (Finset.mem_inter.mp hx).2

private theorem or_subsets {D A B L : Finset (Fin 13)} (h : D = A ∪ B) (hDL : D ⊆ L) :
    A ⊆ L ∧ B ⊆ L := by
  constructor
  · intro x hx
    apply hDL
    rw [h]
    exact Finset.mem_union.mpr (Or.inl hx)
  · intro x hx
    apply hDL
    rw [h]
    exact Finset.mem_union.mpr (Or.inr hx)

private theorem prevOwn (M : LocalModel) (L : Finset (Fin 13)) (w : ℕ)
    (hL : L ≠ Finset.univ) (hs : M.sup w ⊆ L) (hc : 3 ≤ (M.sup w).card)
    (hz : ∀ a b, a ∉ L → b ∉ L → ¬ M.hit w a b) :
    ∃ t, t < w ∧ M.Own L t := by
  classical
  obtain ⟨u, v, hu, hv, hor | hand⟩ :=
    M.step w (by omega) (small_of_proper hL hs)
  · obtain ⟨hsu, _⟩ := hor
    obtain ⟨huL, hvL⟩ := or_subsets hsu hs
    have hbound := Finset.card_union_le (M.sup u) (M.sup v)
    rw [← hsu] at hbound
    by_cases hcu : 2 ≤ (M.sup u).card
    · exact ⟨u, hu, huL, hcu⟩
    · exact ⟨v, hv, hvL, by omega⟩
  · obtain ⟨hsi, hhit⟩ := hand
    obtain ⟨hwu, hwv⟩ := and_subsets hsi
    have hcu := Finset.card_le_card hwu
    have hcv := Finset.card_le_card hwv
    by_cases huL : M.sup u ⊆ L
    · exact ⟨u, hu, huL, by omega⟩
    by_cases hvL : M.sup v ⊆ L
    · exact ⟨v, hv, hvL, by omega⟩
    obtain ⟨a, hau, haL⟩ := exOut huL
    obtain ⟨b, hbv, hbL⟩ := exOut hvL
    exact (hz a b haL hbL ((hhit a b).2
      ⟨M.mono u a b (Or.inl hau), M.mono v a b (Or.inr hbv)⟩)).elim

private theorem missing_prev_or (M : LocalModel) (L : Finset (Fin 13)) (o : ℕ)
    (hL : L ≠ Finset.univ) (hc : (M.sup o).card = 4) (hs : M.sup o ⊆ L)
    (hz : ∀ a b, a ∉ L → b ∉ L → ¬ M.hit o a b)
    (uniq : ∀ i j, i < o → j < o → M.Own L i → M.Own L j → i = j)
    (u v : ℕ) (hu : u < o) (hv : v < o) (he : M.sup o = M.sup u ∪ M.sup v)
    (heval : ∀ a b, M.hit o a b ↔ M.hit u a b ∨ M.hit v a b) : False := by
  obtain ⟨huL, hvL⟩ := or_subsets he hs
  have small (s : ℕ) (hso : s < o) (hsL : M.sup s ⊆ L)
      (hback : ∀ a b, M.hit s a b → M.hit o a b) : (M.sup s).card ≤ 2 := by
    by_contra h
    have h3 : 3 ≤ (M.sup s).card := by omega
    obtain ⟨t, hts, ht⟩ := prevOwn M L s hL hsL h3
      (fun a b ha hb hh => hz a b ha hb (hback a b hh))
    have heq := uniq t s (lt_trans hts hso) hso ht ⟨hsL, by omega⟩
    omega
  have hcu := small u hu huL (fun a b h => (heval a b).2 (Or.inl h))
  have hcv := small v hv hvL (fun a b h => (heval a b).2 (Or.inr h))
  have hbound := Finset.card_union_le (M.sup u) (M.sup v)
  rw [← he] at hbound
  have heq := uniq u v hu hv ⟨huL, by omega⟩ ⟨hvL, by omega⟩
  have hsize : (M.sup o).card = (M.sup v).card := by
    rw [he, heq, Finset.union_self]
  omega

private theorem three_wide (M : LocalModel) (L : Finset (Fin 13)) (o h r : ℕ)
    (hL : L ≠ Finset.univ) (hc : L.card = 4)
    (hz : ∀ a b, a ∉ L → b ∉ L → ¬ M.hit o a b)
    (uniq : ∀ i j, i < o → j < o → M.Own L i → M.Own L j → i = j)
    (hho : h < o) (hro : r < o) (heh : M.sup h = L) (hLr : L ⊆ M.sup r)
    (houter : ∀ a b, M.hit o a b ↔ M.hit h a b ∧ M.hit r a b) :
    ∃ p q r, p < o ∧ q < o ∧ r < o ∧ L ⊂ M.sup p ∧ L ⊂ M.sup q ∧ L ⊂ M.sup r ∧
      M.sup p ∩ M.sup q = L ∧ M.sup p ∩ M.sup r = L ∧ M.sup q ∩ M.sup r = L := by
  classical
  have hch : (M.sup h).card = 4 := by simpa only [heh] using hc
  have hhown : M.Own L h := ⟨by rw [heh], by omega⟩
  have noEarlier (s : ℕ) (hsh : s < h) (hown : M.Own L s) : False := by
    have heq := uniq s h (lt_trans hsh hho) hho hown hhown
    omega
  obtain ⟨p, q, hp, hq, hor | hand⟩ := M.step h (by omega) (by rwa [heh])
  · obtain ⟨he, _⟩ := hor
    obtain ⟨hpL, hqL⟩ := or_subsets he hhown.1
    have hcp : ¬ 2 ≤ (M.sup p).card := fun i => noEarlier p hp ⟨hpL, i⟩
    have hcq : ¬ 2 ≤ (M.sup q).card := fun i => noEarlier q hq ⟨hqL, i⟩
    have hbound := Finset.card_union_le (M.sup p) (M.sup q)
    rw [← he] at hbound
    omega
  · obtain ⟨he, hinner⟩ := hand
    have hpq : M.sup p ∩ M.sup q = L := he.symm.trans heh
    obtain ⟨hLp, hLq⟩ := and_subsets hpq.symm
    have hcp := Finset.card_le_card hLp
    have hcq := Finset.card_le_card hLq
    have hpn : ¬ M.sup p ⊆ L := fun sub => noEarlier p hp ⟨sub, by omega⟩
    have hqn : ¬ M.sup q ⊆ L := fun sub => noEarlier q hq ⟨sub, by omega⟩
    obtain ⟨a, hap, haL⟩ := exOut hpn
    obtain ⟨b, hbq, hbL⟩ := exOut hqn
    have hrn : ¬ M.sup r ⊆ L := by
      intro hr
      have hcr := Finset.card_le_card hLr
      have her := uniq r h hro hho ⟨hr, by omega⟩ hhown
      have hh : M.hit h a b := (hinner a b).2
        ⟨M.mono p a b (Or.inl hap), M.mono q a b (Or.inr hbq)⟩
      apply hz a b haL hbL
      apply (houter a b).2
      exact ⟨hh, by simpa only [her] using hh⟩
    have hpr : M.sup p ∩ M.sup r = L := by
      ext z
      constructor
      · intro hzpr
        obtain ⟨hzp, hzr⟩ := Finset.mem_inter.mp hzpr
        by_contra hzL
        apply hz z b hzL hbL
        exact (houter z b).2 ⟨(hinner z b).2
          ⟨M.mono p z b (Or.inl hzp), M.mono q z b (Or.inr hbq)⟩,
          M.mono r z b (Or.inl hzr)⟩
      · intro hzL
        exact Finset.mem_inter.mpr ⟨hLp hzL, hLr hzL⟩
    have hqr : M.sup q ∩ M.sup r = L := by
      ext z
      constructor
      · intro hzqr
        obtain ⟨hzq, hzr⟩ := Finset.mem_inter.mp hzqr
        by_contra hzL
        apply hz a z haL hzL
        exact (houter a z).2 ⟨(hinner a z).2
          ⟨M.mono p a z (Or.inl hap), M.mono q a z (Or.inr hzq)⟩,
          M.mono r a z (Or.inr hzr)⟩
      · intro hzL
        exact Finset.mem_inter.mpr ⟨hLq hzL, hLr hzL⟩
    exact ⟨p, q, r, lt_trans hp hho, lt_trans hq hho, hro,
      lt_of_le_not_ge hLp hpn, lt_of_le_not_ge hLq hqn,
      lt_of_le_not_ge hLr hrn, hpq, hpr, hqr⟩

theorem local_alt (M : LocalModel) (L : Finset (Fin 13)) (o : ℕ)
    (hcard : L.card = 4) (hs : M.sup o = L)
    (hz : ∀ a b, a ∉ L → b ∉ L → ¬ M.hit o a b) :
    (∃ a b, a < b ∧ b < o ∧ M.Own L a ∧ M.Own L b) ∨
    ((∃ a, a < o ∧ M.Own L a) ∧
      ∃ p q r, p < o ∧ q < o ∧ r < o ∧ L ⊂ M.sup p ∧ L ⊂ M.sup q ∧ L ⊂ M.sup r ∧
        M.sup p ∩ M.sup q = L ∧ M.sup p ∩ M.sup r = L ∧ M.sup q ∩ M.sup r = L) := by
  classical
  have hL : L ≠ Finset.univ := by
    intro he
    rw [he] at hcard
    simpa using hcard
  have hco : (M.sup o).card = 4 := by simpa only [hs] using hcard
  have hsub : M.sup o ⊆ L := by rw [hs]
  by_cases hmany : ∃ a b, a < b ∧ b < o ∧ M.Own L a ∧ M.Own L b
  · exact Or.inl hmany
  right
  refine ⟨prevOwn M L o hL hsub (by omega) hz, ?_⟩
  have uniq : ∀ i j, i < o → j < o → M.Own L i → M.Own L j → i = j := by
    intro i j hi hj hiw hjw
    rcases lt_trichotomy i j with h | h | h
    · exact (hmany ⟨i, j, h, hj, hiw, hjw⟩).elim
    · exact h
    · exact (hmany ⟨j, i, h, hi, hjw, hiw⟩).elim
  obtain ⟨u, v, hu, hv, hor | hand⟩ := M.step o (by omega) (by rwa [hs])
  · exact (missing_prev_or M L o hL hco hsub hz uniq u v hu hv hor.1 hor.2).elim
  · obtain ⟨he, hev⟩ := hand
    have hinter : L = M.sup u ∩ M.sup v := hs.symm.trans he
    obtain ⟨hLu, hLv⟩ := and_subsets hinter
    by_cases huL : M.sup u ⊆ L
    · exact three_wide M L o u v hL hcard hz uniq hu hv
        (Finset.Subset.antisymm huL hLu) hLv hev
    by_cases hvL : M.sup v ⊆ L
    · exact three_wide M L o v u hL hcard hz uniq hv hu
        (Finset.Subset.antisymm hvL hLv) hLu
        (fun a b => (hev a b).trans and_comm)
    obtain ⟨a, hau, haL⟩ := exOut huL
    obtain ⟨b, hbv, hbL⟩ := exOut hvL
    exact (hz a b haL hbL ((hev a b).2
      ⟨M.mono u a b (Or.inl hau), M.mono v a b (Or.inr hbv)⟩)).elim

end LocalModel

end PEqualNP.Outside.L_meta_667_aux

namespace PEqualNP.Outside.L_meta_667_aux

open scoped BigOperators

private theorem filter_empty_of_absent {s : ℕ} (f : Fin 13 → Finset (Fin s))
    (g : Fin s) (h : ∀ w, g ∉ f w) :
    (Finset.univ.filter (fun w : Fin 13 => g ∈ f w)) = ∅ := by
  ext w
  simp [h w]

/-- A gate can supply two half-units, in any one of the three roles. -/
theorem gate_capacity {s : ℕ} (own small large : Fin 13 → Finset (Fin s)) (g : Fin s)
    (ho : (Finset.univ.filter (fun w : Fin 13 => g ∈ own w)).card ≤ 1)
    (hs : (Finset.univ.filter (fun w : Fin 13 => g ∈ small w)).card ≤ 1)
    (hl : (Finset.univ.filter (fun w : Fin 13 => g ∈ large w)).card ≤ 2)
    (hos : ∀ i j, g ∈ own i → g ∈ small j → False)
    (hol : ∀ i j, g ∈ own i → g ∈ large j → False)
    (hsl : ∀ i j, g ∈ small i → g ∈ large j → False) :
    2 * (Finset.univ.filter (fun w : Fin 13 => g ∈ own w)).card +
      2 * (Finset.univ.filter (fun w : Fin 13 => g ∈ small w)).card +
      (Finset.univ.filter (fun w : Fin 13 => g ∈ large w)).card ≤ 2 := by
  classical
  by_cases go : ∃ i, g ∈ own i
  · obtain ⟨i, hi⟩ := go
    rw [filter_empty_of_absent small g (fun j => hos i j hi),
      filter_empty_of_absent large g (fun j => hol i j hi)]
    simp only [Finset.card_empty, Nat.mul_zero, Nat.add_zero]
    omega
  · rw [filter_empty_of_absent own g (fun i hi => go ⟨i, hi⟩)]
    by_cases gs : ∃ i, g ∈ small i
    · obtain ⟨i, hi⟩ := gs
      rw [filter_empty_of_absent large g (fun j => hsl i j hi)]
      simp only [Finset.card_empty, Nat.mul_zero, Nat.zero_add, Nat.add_zero]
      omega
    · rw [filter_empty_of_absent small g (fun i hi => gs ⟨i, hi⟩)]
      simpa only [Finset.card_empty, Nat.mul_zero, Nat.zero_add] using hl

private theorem line_gate_incidences {s : ℕ} (f : Fin 13 → Finset (Fin s)) :
    (∑ w : Fin 13, (f w).card) =
      ∑ g : Fin s, (Finset.univ.filter (fun w : Fin 13 => g ∈ f w)).card := by
  classical
  have row (w : Fin 13) : Finset.univ.filter (fun g : Fin s => g ∈ f w) = f w := by
    ext g
    simp
  simpa only [Finset.bipartiteAbove, Finset.bipartiteBelow, row] using
    (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := (Finset.univ : Finset (Fin 13))) (t := (Finset.univ : Finset (Fin s)))
      (fun (w : Fin 13) (g : Fin s) => g ∈ f w))

/-- Each line receives at least six half-units and each physical gate supplies at most two. -/
theorem count_gates {s : ℕ} (own small large : Fin 13 → Finset (Fin s))
    (hown : ∀ w, 2 ≤ (own w).card)
    (hdef : ∀ w, (own w).card = 2 → (small w).Nonempty ∨ 3 ≤ (large w).card)
    (hcap : ∀ g : Fin s,
      2 * (Finset.univ.filter (fun w : Fin 13 => g ∈ own w)).card +
        2 * (Finset.univ.filter (fun w : Fin 13 => g ∈ small w)).card +
        (Finset.univ.filter (fun w : Fin 13 => g ∈ large w)).card ≤ 2) : 39 ≤ s := by
  classical
  have hrow (w : Fin 13) :
      6 ≤ 2 * (own w).card + 2 * (small w).card + (large w).card := by
    have e := hown w
    by_cases h : (own w).card = 2
    · rcases hdef w h with hs | hl
      · have := hs.card_pos
        omega
      · omega
    · omega
  have lo := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 13))) (fun w _ => hrow w)
  have hi := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin s))) (fun g _ => hcap g)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, Nat.nsmul_eq_mul] at lo hi
  rw [line_gate_incidences own, line_gate_incidences small, line_gate_incidences large] at lo
  omega

end PEqualNP.Outside.L_meta_667_aux

namespace PEqualNP.Outside.L_meta_667_aux

def line (w : Fin 13) : Finset (Fin 13) :=
  ({0, 1, 3, 9} : Finset (Fin 13)).image (fun u => u + w)

lemma line_sizes : ∀ w : Fin 13, (line w).card = 4 := by decide

set_option maxRecDepth 16000 in
set_option maxHeartbeats 800000 in
lemma line_pairs :
    ∀ u v : Fin 13, u ≠ v → ((line u) ∩ (line v)).card ≤ 1 := by decide

lemma atMostOne {α : Type*} [DecidableEq α] (s : Finset α)
    (h : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → False) : s.card ≤ 1 := by
  by_contra! hc
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hc
  exact h x hx y hy hxy

lemma atMostTwo {α : Type*} [DecidableEq α] (s : Finset α)
    (h : ∀ x ∈ s, ∀ y ∈ s, ∀ z ∈ s, x ≠ y → x ≠ z → y ≠ z → False) :
    s.card ≤ 2 := by
  by_contra! hc
  obtain ⟨z, hz⟩ := Finset.card_pos.mp (show 0 < s.card by omega)
  have her := Finset.card_erase_of_mem hz
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp
    (show 1 < (s.erase z).card by omega)
  exact h x (Finset.mem_erase.mp hx).2 y (Finset.mem_erase.mp hy).2 z hz
    hxy (Finset.mem_erase.mp hx).1 (Finset.mem_erase.mp hy).1

lemma fitTwo {u v : Fin 13} (huv : u ≠ v) (S : Finset (Fin 13))
    (hu : line u ⊆ S) (hv : line v ⊆ S) : 7 ≤ S.card := by
  have h1 := Finset.card_union_add_card_inter (line u) (line v)
  have h2 := Finset.card_le_card (Finset.union_subset hu hv)
  have h3 := line_pairs u v huv
  have h4 := line_sizes u
  have h5 := line_sizes v
  omega

lemma fitThree {u v w : Fin 13} (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (S : Finset (Fin 13)) (hu : line u ⊆ S) (hv : line v ⊆ S) (hw : line w ⊆ S) :
    9 ≤ S.card := by
  have h1 := fitTwo huv (line u ∪ line v) Finset.subset_union_left Finset.subset_union_right
  have h2 := Finset.card_union_add_card_inter (line u ∪ line v) (line w)
  have h3 : ((line u ∪ line v) ∩ line w).card ≤ 2 := by
    have hsub : (line u ∪ line v) ∩ line w ⊆
        (line u ∩ line w) ∪ (line v ∩ line w) := by
      intro p hp
      simp only [Finset.mem_inter, Finset.mem_union] at hp ⊢
      tauto
    have ha := Finset.card_le_card hsub
    have hb := Finset.card_union_le (line u ∩ line w) (line v ∩ line w)
    have hc := line_pairs u w huw
    have hd := line_pairs v w hvw
    omega
  have h4 := Finset.card_le_card (Finset.union_subset (Finset.union_subset hu hv) hw)
  have h5 := line_sizes w
  omega

lemma threeSizes (P Q R L : Finset (Fin 13))
    (hpq : P ∩ Q = L) (hpr : P ∩ R = L) (hqr : Q ∩ R = L) (hl : L.card = 4)
    (hp : 7 ≤ P.card) (hq : 7 ≤ Q.card) (hr : 7 ≤ R.card) :
    P.card = 7 ∧ Q.card = 7 ∧ R.card = 7 := by
  have h1 := Finset.card_union_add_card_inter P Q
  rw [hpq, hl] at h1
  have h2 := Finset.card_union_add_card_inter (P ∪ Q) R
  have hh : (P ∪ Q) ∩ R = L := by
    ext x
    have a : (x ∈ P ∧ x ∈ R) ↔ x ∈ L := by rw [← Finset.mem_inter, hpr]
    have b : (x ∈ Q ∧ x ∈ R) ↔ x ∈ L := by rw [← Finset.mem_inter, hqr]
    simp only [Finset.mem_inter, Finset.mem_union]
    tauto
  rw [hh, hl] at h2
  have cap : (P ∪ Q ∪ R).card ≤ 13 := by
    simpa using (Finset.card_le_univ (P ∪ Q ∪ R))
  omega

end PEqualNP.Outside.L_meta_667_aux

namespace PEqualNP.Outside.L_meta_667_aux

open PEqualNP.CircuitLowerBounds

abbrev Assignment667 := Fin 13 → Bool
abbrev Value667 := Assignment667 → Bool

def zero667 : Value667 := fun _ => false
def one667 : Value667 := fun _ => true
def input667 (i : Fin 13) : Value667 := fun x => x i

def val667 (ws : List Value667) : ℕ → Value667
  | 0 => zero667
  | 1 => one667
  | i + 2 => ws.getD i zero667

def ref667 (ws : List Value667) (i : ℕ) : ℕ :=
  if i < ws.length then i + 2 else 0

private lemma ref667_lt (ws : List Value667) (i : ℕ) :
    ref667 ws i < ws.length + 2 := by
  unfold ref667
  split <;> omega

private lemma val667_ref (ws : List Value667) (i : ℕ) :
    val667 ws (ref667 ws i) = ws.getD i zero667 := by
  unfold ref667
  split
  · rfl
  · rename_i h
    exact (List.getD_eq_default _ _ (by omega)).symm

private lemma val667_append_before (ws : List Value667) (f : Value667) (w : ℕ)
    (hw : w < ws.length + 2) : val667 (ws ++ [f]) w = val667 ws w := by
  rcases w with _ | w
  · rfl
  rcases w with _ | i
  · rfl
  change (ws ++ [f]).getD i zero667 = ws.getD i zero667
  exact List.getD_append _ _ _ _ (by omega)

private lemma val667_append_last (ws : List Value667) (f : Value667) :
    val667 (ws ++ [f]) (ws.length + 2) = f := by
  change (ws ++ [f]).getD ws.length zero667 = f
  simp

private lemma val667_large (ws : List Value667) (w : ℕ) (hw : ws.length + 2 ≤ w) :
    val667 ws w = zero667 := by
  rcases w with _ | w
  · omega
  rcases w with _ | i
  · omega
  change ws.getD i zero667 = zero667
  exact List.getD_eq_default _ _ (by omega)

def gate667 (ws : List Value667) (g : Gate) : Value667 :=
  fun x => g.op.eval (g.inputs.map fun i => ws.getD i zero667 x)

def ok667 (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

def shape667 (W : ℕ → Value667) (w : ℕ) : Prop :=
  W w = zero667 ∨ W w = one667 ∨ (∃ p, W w = input667 p) ∨
    ∃ u v, u < w ∧ v < w ∧
      ((∀ x, W w x = (W u x || W v x)) ∨
       (∀ x, W w x = (W u x && W v x)))

private lemma gate667_inputs (ws : List Value667) (g : Gate) (hg : ok667 g) :
    ∃ u v, u < ws.length + 2 ∧ v < ws.length + 2 ∧
      ((∀ x, gate667 ws g x = (val667 ws u x || val667 ws v x)) ∨
       (∀ x, gate667 ws g x = (val667 ws u x && val667 ws v x))) := by
  obtain ⟨op, ins⟩ := g
  rcases hg with ⟨hop, hlen⟩
  change op = GateOp.and ∨ op = GateOp.or at hop
  change ins.length ≤ 2 at hlen
  rcases ins with _ | ⟨i, rest⟩
  · rcases hop with rfl | rfl
    · exact ⟨1, 1, by omega, by omega, Or.inr (fun _ => rfl)⟩
    · exact ⟨0, 0, by omega, by omega, Or.inl (fun _ => rfl)⟩
  rcases rest with _ | ⟨j, tail⟩
  · refine ⟨ref667 ws i, ref667 ws i, ref667_lt ws i, ref667_lt ws i, Or.inl ?_⟩
    intro x
    rw [val667_ref]
    rcases hop with rfl | rfl <;> simp [gate667, GateOp.eval]
  rcases tail with _ | ⟨k, tail⟩
  · refine ⟨ref667 ws i, ref667 ws j, ref667_lt ws i, ref667_lt ws j, ?_⟩
    rcases hop with rfl | rfl
    · right
      intro x
      simp [gate667, GateOp.eval, val667_ref]
    · left
      intro x
      simp [gate667, GateOp.eval, val667_ref]
  · simp only [List.length_cons] at hlen
    omega

private lemma shape667_transport {W W' : ℕ → Value667} {w : ℕ}
    (h : ∀ i, i ≤ w → W' i = W i) (hs : shape667 W w) : shape667 W' w := by
  unfold shape667 at *
  rw [h w (by omega)]
  rcases hs with hh | hh | hh | ⟨u, v, hu, hv, hgate⟩
  · exact Or.inl hh
  · exact Or.inr (Or.inl hh)
  · exact Or.inr (Or.inr (Or.inl hh))
  · refine Or.inr (Or.inr (Or.inr ⟨u, v, hu, hv, ?_⟩))
    rw [h u (by omega), h v (by omega)]
    exact hgate

private lemma append667_shapes (ws : List Value667) (g : Gate) (hg : ok667 g)
    (hs : ∀ w, shape667 (val667 ws) w) :
    ∀ w, shape667 (val667 (ws ++ [gate667 ws g])) w := by
  intro w
  rcases lt_trichotomy w (ws.length + 2) with hw | hw | hw
  · apply shape667_transport (W := val667 ws) _ (hs w)
    exact fun i hi => val667_append_before ws (gate667 ws g) i (by omega)
  · subst w
    obtain ⟨u, v, hu, hv, hh⟩ := gate667_inputs ws g hg
    refine Or.inr (Or.inr (Or.inr ⟨u, v, hu, hv, ?_⟩))
    rw [val667_append_last, val667_append_before _ _ _ hu, val667_append_before _ _ _ hv]
    exact hh
  · exact Or.inl (val667_large _ _ (by simp; omega))

def init667 : List Value667 := List.ofFn input667

private lemma init667_shapes (w : ℕ) : shape667 (val667 init667) w := by
  rcases w with _ | w
  · exact Or.inl rfl
  rcases w with _ | i
  · exact Or.inr (Or.inl rfl)
  by_cases hi : i < 13
  · refine Or.inr (Or.inr (Or.inl ⟨⟨i, hi⟩, ?_⟩))
    change (List.ofFn input667).getD i zero667 = _
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]
  · exact Or.inl (val667_large _ _ (by simp [init667]; omega))

def run667 (gs : List Gate) (ws : List Value667) : List Value667 :=
  gs.foldl (fun l g => l ++ [gate667 l g]) ws

def all667 (gs : List Gate) : List Value667 := run667 gs init667

private lemma run667_shapes (gs : List Gate) (hok : ∀ g ∈ gs, ok667 g) :
    ∀ ws, (∀ w, shape667 (val667 ws) w) →
     ∀ w, shape667 (val667 (run667 gs ws)) w := by
  induction gs with
  | nil => exact fun _ h => h
  | cons g gs ih =>
    intro ws h
    exact ih (fun t ht => hok t (by simp [ht])) _
      (append667_shapes ws g (hok g (by simp)) h)

private lemma run667_prefix (gs : List Gate) :
    ∀ ws, ∃ t, run667 gs ws = ws ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => exact fun ws => ⟨[], by simp [run667], rfl⟩
  | cons g gs ih =>
    intro ws
    obtain ⟨t, ht, hl⟩ := ih (ws ++ [gate667 ws g])
    refine ⟨gate667 ws g :: t, ?_, by simp [hl]⟩
    change run667 gs (ws ++ [gate667 ws g]) = _
    rw [ht]
    simp

private lemma read667_map (ws : List Value667) (x : Assignment667) (i : ℕ) :
    (ws.map (fun f => f x)).getD i false = ws.getD i zero667 x := by
  exact List.getD_map ws zero667 (n := i) (fun f => f x)

private lemma run667_eval (gs : List Gate) (x : Assignment667) :
    ∀ ws, (run667 gs ws).map (fun f => f x) =
      gs.foldl (fun l g => l ++ [g.op.eval (g.inputs.map fun i => l.getD i false)])
        (ws.map (fun f => f x)) := by
  induction gs with
  | nil => intro ws; rfl
  | cons g gs ih =>
    intro ws
    change (run667 gs (ws ++ [gate667 ws g])).map _ = _
    rw [ih]
    simp only [List.foldl_cons, List.map_append, List.map_cons, List.map_nil, gate667,
      read667_map]

lemma all667_length (gs : List Gate) : (all667 gs).length = 13 + gs.length := by
  obtain ⟨t, ht, hl⟩ := run667_prefix gs init667
  have hinit : init667.length = 13 := rfl
  unfold all667
  rw [ht, List.length_append, hinit, hl]

lemma circuit667_eval (gs : List Gate) (out : ℕ) (x : Assignment667) :
    val667 (all667 gs) (ref667 (all667 gs) out) x =
      (Circuit.mk gs out).eval (List.ofFn x) := by
  rw [val667_ref, ← read667_map, all667, run667_eval]
  simp [init667, input667, Circuit.eval, Circuit.wires]

def single667 (p : Fin 13) : Assignment667 := fun i => decide (i = p)
def pair667 (p q : Fin 13) : Assignment667 := fun i => decide (i = p ∨ i = q)
def support667 (f : Value667) : Finset (Fin 13) :=
  Finset.univ.filter (fun p => f (single667 p) = true)

@[simp] lemma mem_support667 (f : Value667) (p : Fin 13) :
    p ∈ support667 f ↔ f (single667 p) = true := by simp [support667]

@[simp] private lemma support667_zero : support667 zero667 = ∅ := by
  ext p
  simp [zero667]

@[simp] private lemma support667_one : support667 one667 = Finset.univ := by
  ext p
  simp [one667]

@[simp] private lemma support667_input (i : Fin 13) : support667 (input667 i) = {i} := by
  ext p
  simp [input667, single667, eq_comm]

private lemma value667_mono (W : ℕ → Value667) (hs : ∀ w, shape667 W w) :
    ∀ w (x y : Assignment667), (∀ p, x p = true → y p = true) →
      W w x = true → W w y = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro x y hxy hw
    rcases hs w with hh | hh | ⟨p, hh⟩ | ⟨u, v, hu, hv, hor | hand⟩
    · simp [hh, zero667] at hw
    · simp [hh, one667]
    · rw [hh] at hw ⊢
      exact hxy p hw
    · rw [hor x, Bool.or_eq_true] at hw
      rw [hor y, Bool.or_eq_true]
      exact hw.imp (ih u hu x y hxy) (ih v hv x y hxy)
    · rw [hand x, Bool.and_eq_true] at hw
      rw [hand y, Bool.and_eq_true]
      exact ⟨ih u hu x y hxy hw.1, ih v hv x y hxy hw.2⟩

def circuitLocalModel (gs : List Gate) (hok : ∀ g ∈ gs, ok667 g) : LocalModel := by
  refine LocalModel.mk (fun w => support667 (val667 (all667 gs) w))
    (fun w p q => val667 (all667 gs) w (pair667 p q) = true) ?_ ?_
  ·
    intro w p q h
    have hmono := value667_mono _ (run667_shapes gs hok init667 init667_shapes) w
    rcases h with h | h
    · apply hmono (single667 p) (pair667 p q) _ ((mem_support667 ..).mp h)
      intro i hi
      simp [single667] at hi
      simp [pair667, hi]
    · apply hmono (single667 q) (pair667 p q) _ ((mem_support667 ..).mp h)
      intro i hi
      simp [single667] at hi
      simp [pair667, hi]
  ·
    intro w hcard hproper
    let W := val667 (all667 gs)
    have hs : shape667 W w := run667_shapes gs hok init667 init667_shapes w
    change 2 ≤ (support667 (W w)).card at hcard
    change support667 (W w) ≠ Finset.univ at hproper
    rcases hs with hh | hh | ⟨p, hh⟩ | ⟨u, v, hu, hv, hor | hand⟩
    · simp [hh] at hcard
    · simp [hh] at hproper
    · simp [hh] at hcard
    · refine ⟨u, v, hu, hv, Or.inl ⟨?_, ?_⟩⟩
      · ext i
        change i ∈ support667 (W w) ↔ i ∈ support667 (W u) ∪ support667 (W v)
        simp [hor (single667 i)]
      · intro a b
        change W w (pair667 a b) = true ↔ _
        rw [hor, Bool.or_eq_true]
    · refine ⟨u, v, hu, hv, Or.inr ⟨?_, ?_⟩⟩
      · ext i
        change i ∈ support667 (W w) ↔ i ∈ support667 (W u) ∩ support667 (W v)
        simp [hand (single667 i)]
      · intro a b
        change W w (pair667 a b) = true ↔ _
        rw [hand, Bool.and_eq_true]

lemma circuit667_range (gs : List Gate) (hok : ∀ g ∈ gs, ok667 g) (w : ℕ)
    (hc : 2 ≤ ((circuitLocalModel gs hok).sup w).card)
    (hp : (circuitLocalModel gs hok).sup w ≠ Finset.univ) :
    15 ≤ w ∧ w < 15 + gs.length := by
  change 2 ≤ (support667 (val667 (all667 gs) w)).card at hc
  change support667 (val667 (all667 gs) w) ≠ Finset.univ at hp
  constructor
  · by_contra hn
    rcases w with _ | w
    · simp [val667] at hc
    rcases w with _ | i
    · simp [val667] at hp
    have hi : i < 13 := by omega
    obtain ⟨t, ht, _⟩ := run667_prefix gs init667
    have hh : val667 (all667 gs) (i + 2) = input667 ⟨i, hi⟩ := by
      change (run667 gs init667).getD i zero667 = _
      rw [ht, List.getD_append _ _ _ _ (by simpa [init667] using hi)]
      change (List.ofFn input667).getD i zero667 = _
      rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]
    simp [hh] at hc
  · by_contra hn
    have he : val667 (all667 gs) w = zero667 :=
      val667_large _ _ (by rw [all667_length]; omega)
    simp [he] at hc

def isLight667 (x : Assignment667) : Prop :=
  ∀ i j k, x i = true → x j = true → x k = true → i = j ∨ j = k ∨ i = k

lemma single667_light (p : Fin 13) : isLight667 (single667 p) := by
  intro i j k hi hj hk
  simp [single667] at hi hj hk
  simp_all

lemma pair667_light (p q : Fin 13) : isLight667 (pair667 p q) := by
  intro i j k hi hj hk
  simp [pair667] at hi hj hk
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> rcases hk with rfl | rfl <;> simp

lemma circuit667_output (gs : List Gate) (hok : ∀ g ∈ gs, ok667 g)
    (out : ℕ) (L : Finset (Fin 13))
    (correct : ∀ x : Assignment667, isLight667 x →
      (Circuit.mk gs out).eval (List.ofFn x) = decide (∃ i ∈ L, x i = true)) :
    (circuitLocalModel gs hok).sup (ref667 (all667 gs) out) = L ∧
      ∀ a b, (circuitLocalModel gs hok).hit (ref667 (all667 gs) out) a b ↔ a ∈ L ∨ b ∈ L := by
  constructor
  · ext p
    change p ∈ support667 (val667 (all667 gs) (ref667 (all667 gs) out)) ↔ _
    rw [mem_support667, circuit667_eval, correct _ (single667_light p)]
    simp [single667]
  · intro a b
    change val667 (all667 gs) (ref667 (all667 gs) out) (pair667 a b) = true ↔ _
    rw [circuit667_eval, correct _ (pair667_light a b)]
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨i, hi, hx⟩
      simp [pair667] at hx
      rcases hx with rfl | rfl
      · exact Or.inl hi
      · exact Or.inr hi
    · rintro (ha | hb)
      · exact ⟨a, ha, by simp [pair667]⟩
      · exact ⟨b, hb, by simp [pair667]⟩

end PEqualNP.Outside.L_meta_667_aux

namespace PEqualNP.Outside.L_meta_667_aux

private lemma indexOfWire {s z : ℕ} (lo : 15 ≤ z) (hi : z < 15+s) :
    ∃ g : Fin s, g.val + 15 = z :=
  ⟨⟨z-15, by omega⟩, by dsimp; omega⟩

private lemma capCard2 {s : ℕ} (A : Finset (Fin s)) {a b : Fin s}
    (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b) : 2 ≤ A.card := by
  exact Finset.one_lt_card.mpr ⟨a,ha,b,hb,hab⟩

private lemma capCard3 {s : ℕ} (A : Finset (Fin s)) {a b c : Fin s}
    (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : 3 ≤ A.card := by
  exact Finset.two_lt_card_iff.mpr ⟨a,b,c,ha,hb,hc,hab,hac,hbc⟩

private theorem modelCount (M : LocalModel) (s : ℕ)
    (rangeOk : ∀ z, 2 ≤ (M.sup z).card → M.sup z ≠ Finset.univ → 15 ≤ z ∧ z < 15+s)
    (out : Fin 13 → ℕ) (hs : ∀ w, M.sup (out w) = line w)
    (safe : ∀ w a b, a ∉ line w → b ∉ line w → ¬ M.hit (out w) a b) : 39 ≤ s := by
  classical
  let D (g : Fin s) := M.sup (g.val + 15)
  let E (w : Fin 13) := Finset.univ.filter fun g : Fin s => M.Own (line w) (g.val + 15)
  let B (w : Fin 13) := Finset.univ.filter fun g : Fin s =>
    line w ⊆ D g ∧ 5 ≤ (D g).card ∧ (D g).card ≤ 6
  let T (w : Fin 13) := Finset.univ.filter fun g : Fin s =>
    line w ⊆ D g ∧ (D g).card = 7
  have memE (w : Fin 13) (g : Fin s) :
      g ∈ E w ↔ M.Own (line w) (g.val + 15) := by simp [E]
  have memB (w : Fin 13) (g : Fin s) :
      g ∈ B w ↔ line w ⊆ D g ∧ 5 ≤ (D g).card ∧ (D g).card ≤ 6 := by simp [B]
  have memT (w : Fin 13) (g : Fin s) :
      g ∈ T w ↔ line w ⊆ D g ∧ (D g).card = 7 := by simp [T]
  have asGate (z : ℕ) (hlo : 2 ≤ (M.sup z).card) (hhi : (M.sup z).card < 13) :
      ∃ g : Fin s, g.val + 15 = z := by
    have hu : M.sup z ≠ Finset.univ := by
      intro e
      simp [e] at hhi
    obtain ⟨lo, hi⟩ := rangeOk z hlo hu
    exact indexOfWire lo hi
  have ownIdx (w : Fin 13) (z : ℕ) (h : M.Own (line w) z) :
      ∃ g : Fin s, g.val + 15 = z ∧ g ∈ E w := by
    have H := Finset.card_le_card h.1
    have HL := line_sizes w
    obtain ⟨g, hg⟩ := asGate z h.2 (by omega)
    exact ⟨g,hg,(memE w g).mpr (hg.symm ▸ h)⟩
  have row (w : Fin 13) :
      3 ≤ (E w).card ∨ (2 ≤ (E w).card ∧ ((B w).Nonempty ∨ 3 ≤ (T w).card)) := by
    let L := line w
    let o := out w
    have HL : L.card = 4 := line_sizes w
    have hout : M.Own (line w) o := by
      constructor
      · rw [show M.sup o = line w from hs w]
      · rw [show M.sup o = line w from hs w, line_sizes]
        decide
    obtain ⟨gout, egout, mgout⟩ := ownIdx w o hout
    rcases M.local_alt (line w) o (line_sizes w) (hs w) (safe w) with
      ⟨a,b,hab,hbo,ha,hb⟩ | ⟨⟨a,hao,ha⟩,p,q,r,_,_,_,hp,hq,hr,hpq,hpr,hqr⟩
    · obtain ⟨ga,ea,ma⟩ := ownIdx w a ha
      obtain ⟨gb,eb,mb⟩ := ownIdx w b hb
      exact Or.inl (capCard3 _ ma mb mgout
        (by rintro rfl; omega) (by rintro rfl; omega) (by rintro rfl; omega))
    · obtain ⟨ga,ea,ma⟩ := ownIdx w a ha
      refine Or.inr ⟨capCard2 _ ma mgout (by rintro rfl; omega), ?_⟩
      have small (z : ℕ) (hz : line w ⊂ M.sup z) (hz6 : (M.sup z).card ≤ 6) :
          (B w).Nonempty := by
        have h5 := Finset.card_lt_card hz
        rw [line_sizes] at h5
        obtain ⟨g, eg⟩ := asGate z (by omega) (by omega)
        refine ⟨g, (memB w g).mpr ?_⟩
        change line w ⊆ M.sup (g.val+15) ∧ 5 ≤ (M.sup (g.val+15)).card ∧ (M.sup (g.val+15)).card ≤ 6
        rw [eg]
        exact ⟨hz.1,by omega,hz6⟩
      by_cases lp : (M.sup p).card ≤ 6
      · exact Or.inl (small p hp lp)
      by_cases lq : (M.sup q).card ≤ 6
      · exact Or.inl (small q hq lq)
      by_cases lr : (M.sup r).card ≤ 6
      · exact Or.inl (small r hr lr)
      have sz := threeSizes _ _ _ _ hpq hpr hqr (line_sizes w)
        (by omega) (by omega) (by omega)
      have large (z : ℕ) (hz : line w ⊂ M.sup z) (hz7 : (M.sup z).card = 7) :
          ∃ g : Fin s, g.val+15 = z ∧ g ∈ T w := by
        obtain ⟨g, eg⟩ := asGate z (by omega) (by omega)
        refine ⟨g,eg,(memT w g).mpr ?_⟩
        change line w ⊆ M.sup (g.val+15) ∧ (M.sup (g.val+15)).card = 7
        rw [eg]
        exact ⟨hz.1,hz7⟩
      have diff (i j : ℕ) (h : M.sup i ∩ M.sup j = line w) (hwide : line w ⊂ M.sup i) : i ≠ j := by
        rintro rfl
        simp only [Finset.inter_self] at h
        exact (ne_of_lt hwide) h.symm
      have dpq := diff p q hpq hp
      have dpr := diff p r hpr hp
      have dqr := diff q r hqr hq
      obtain ⟨gp,ep,mp⟩ := large p hp sz.1
      obtain ⟨gq,eq,mq⟩ := large q hq sz.2.1
      obtain ⟨gr,er,mr⟩ := large r hr sz.2.2
      exact Or.inr (capCard3 _ mp mq mr
        (by rintro rfl; omega) (by rintro rfl; omega) (by rintro rfl; omega))
  apply count_gates E B T
  · intro w
    rcases row w with h | ⟨h,_⟩ <;> omega
  · intro w hw
    rcases row w with h | ⟨_,h⟩
    · omega
    · exact h
  · intro g
    apply gate_capacity E B T g
    · apply atMostOne
      intro i hi j hj hij
      have a := (memE i g).mp (Finset.mem_filter.mp hi).2
      have b := (memE j g).mp (Finset.mem_filter.mp hj).2
      have sub : M.sup (g.val + 15) ⊆ line i ∩ line j := Finset.subset_inter a.1 b.1
      have t1 := Finset.card_le_card sub
      have t2 := line_pairs i j hij
      exact (by have := a.2; omega)
    · apply atMostOne
      intro i hi j hj hij
      have a := (memB i g).mp (Finset.mem_filter.mp hi).2
      have b := (memB j g).mp (Finset.mem_filter.mp hj).2
      have t := fitTwo hij (D g) a.1 b.1
      have t2 := a.2.2
      omega
    · apply atMostTwo
      intro i hi j hj k hk hij hik hjk
      have a := (memT i g).mp (Finset.mem_filter.mp hi).2
      have b := (memT j g).mp (Finset.mem_filter.mp hj).2
      have c := (memT k g).mp (Finset.mem_filter.mp hk).2
      have t := fitThree hij hik hjk (D g) a.1 b.1 c.1
      have t2 := a.2
      omega
    · intro i j hi hj
      have t := Finset.card_le_card ((memE i g).mp hi).1
      change (D g).card ≤ _ at t
      have u := ((memB j g).mp hj).2.1
      rw [line_sizes] at t
      omega
    · intro i j hi hj
      have t := Finset.card_le_card ((memE i g).mp hi).1
      change (D g).card ≤ _ at t
      have u := ((memT j g).mp hj).2
      rw [line_sizes] at t
      omega
    · intro i j hi hj
      have t := ((memB i g).mp hi).2.2
      have u := ((memT j g).mp hj).2
      omega

end PEqualNP.Outside.L_meta_667_aux

theorem PEqualNP.Outside.L_meta_667 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin 13 → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin 13) (x : Fin 13 → Bool), (∀ i j k : Fin 13, x i = true → x j = true → x k = true → i = j ∨ j = k ∨ i = k) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ (({0, 1, 3, 9} : Finset (Fin 13)).image (fun u => u + w)), x v = true)) → 39 ≤ gates.length := by
  intro gs out hok correct
  let M := PEqualNP.Outside.L_meta_667_aux.circuitLocalModel gs hok
  let o (w : Fin 13) := PEqualNP.Outside.L_meta_667_aux.ref667 (PEqualNP.Outside.L_meta_667_aux.all667 gs) (out w)
  have H (w : Fin 13) := PEqualNP.Outside.L_meta_667_aux.circuit667_output gs hok (out w) (PEqualNP.Outside.L_meta_667_aux.line w) (correct w)
  exact PEqualNP.Outside.L_meta_667_aux.modelCount M gs.length (PEqualNP.Outside.L_meta_667_aux.circuit667_range gs hok) o
    (fun w => (H w).1) (fun w a b ha hb h => ((H w).2 a b |>.mp h).elim ha hb)
