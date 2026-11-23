import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_700_aux

abbrev W := BitVec 108

def bit (k : Fin 108) (w : W) : Bool := w.getLsbD k.val

def rawInputs : List W :=
  [633822886984823975214363968001, 2413138481558843201995874,
   2417842429535473200466308, 323885963880500264155966194405544,
   324517315718387453247965072892240]

def inputs : List W := rawInputs
def goal : W := (-1 : BitVec 54) ++ (0 : BitVec 54)

abbrev wide (w : W) : Prop :=
  ∃ u v : Fin 5, u ≠ v ∧ w.getLsbD u.val = true ∧ w.getLsbD v.val = true

def isWide (w : W) : Bool := decide (wide w)

def edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (1, 2), (0, 3), (0, 4), (3, 4)]

def assignment (k : Fin 108) (i : Fin 5) : Bool := bit k (rawInputs.getD i.val 0)

theorem input_rows (k : Fin 108) : List.ofFn (assignment k) = rawInputs.map (bit k) := by rfl

theorem graph_rows : ∀ k : Fin 108, (∃ u v : Fin 5, (u.val, v.val) ∈ edges ∧
    assignment k u = true ∧ assignment k v = true) ↔ bit k goal = true := by
  decide +kernel

theorem single_rows (u : Fin 5) :
    assignment ⟨u.val, by omega⟩ = (fun i => decide (i = u)) := by
  revert u
  decide +kernel

end PEqualNP.Outside.L_meta_700_aux

-- The finite-frontier representation, commutative pair enumeration and bit-separation
-- lemmas adapt the Apache-2.0 public L-meta-618 proof in brilliant-hq/pequalnp-proofs
-- PR 795, commit 17e8ea58508441e67cf2da313fdd45e4f701064d. The weighted reachability,
-- budget accounting and certificate here concern L-meta-700.
namespace PEqualNP.Outside.L_meta_700_aux

def orWeight (w : W) : ℕ := if isWide w then 1 else 2
def valOf (q : Bool) (a b : W) : W := if q then a ||| b else a &&& b
def charge (q : Bool) (a b : W) : ℕ := if q then orWeight (a ||| b) else 1

theorem charge_pos (q : Bool) (a b : W) : 0 < charge q a b := by
  cases q with
  | false => simp [charge]
  | true => simp only [charge, ite_true, orWeight]; split <;> decide

theorem swap_val (q : Bool) (a b : W) : valOf q b a = valOf q a b := by
  cases q <;> simp [valOf, BitVec.and_comm, BitVec.or_comm]

theorem swap_charge (q : Bool) (a b : W) : charge q b a = charge q a b := by
  cases q <;> simp [charge, BitVec.or_comm]

-- Impredicative closure under the three weighted construction rules.
def Build (k : ℕ) (s : Finset W) : Prop :=
  ∀ P : ℕ → Finset W → Prop,
    (∀ {v}, goal ∈ v → P 0 v) →
    (∀ {n v}, P n v → P (n+1) v) →
    (∀ {n v a b}, a ∈ v → b ∈ v → a ≠ b → ∀ q : Bool,
       P n (insert (valOf q a b) v) → P (n + charge q a b) v) → P k s

namespace Build

theorem done {s} (hg : goal ∈ s) : Build 0 s :=
  fun _ base _ _ => base hg

theorem pad {k s} (h : Build k s) : Build (k+1) s :=
  fun P base grow join => grow (h P base grow join)

theorem step {k s a b} (ha : a ∈ s) (hb : b ∈ s) (hne : a ≠ b) (q : Bool)
    (h : Build k (insert (valOf q a b) s)) : Build (k + charge q a b) s :=
  fun P base grow join => join ha hb hne q (h P base grow join)

theorem induct
    {motive : (k : ℕ) → (s : Finset W) → Build k s → Prop}
    (done : ∀ {s} (hg : goal ∈ s), motive 0 s (Build.done hg))
    (pad : ∀ {k s} (h : Build k s), motive k s h → motive (k+1) s (Build.pad h))
    (step : ∀ {k s a b} (ha : a ∈ s) (hb : b ∈ s) (hne : a ≠ b) (q : Bool)
      (h : Build k (insert (valOf q a b) s)), motive k _ h →
      motive (k + charge q a b) s (Build.step ha hb hne q h))
    {k s} (h : Build k s) : motive k s h := by
  apply (show (∃ e : Build k s, motive k s e) → motive k s h from fun ⟨_,w⟩ => w)
  apply h (fun n v => ∃ e : Build n v, motive n v e)
  · intro v hv; exact ⟨Build.done hv, done hv⟩
  · rintro n v ⟨e, ih⟩; exact ⟨Build.pad e, pad e ih⟩
  · rintro n v a b ha hb hne q ⟨e, ih⟩
    exact ⟨Build.step ha hb hne q e, step ha hb hne q e ih⟩

end Build



theorem build_done {s} (h : goal ∈ s) : Build 0 s := .done h
theorem build_weaken {k l s} (hle : k ≤ l) (h : Build k s) : Build l s := by
  induction hle with
  | refl => exact h
  | step _ ih => exact .pad ih
theorem build_and {a b s k} (ha : a ∈ s) (hb : b ∈ s) (hne : a ≠ b)
    (h : Build k (insert (a &&& b) s)) : Build (k+1) s :=
  .step ha hb hne false h
theorem build_or {a b s k} (ha : a ∈ s) (hb : b ∈ s) (hne : a ≠ b)
    (h : Build k (insert (a ||| b) s)) : Build (k+orWeight (a ||| b)) s :=
  .step ha hb hne true h

-- The corresponding least closure for the live frontier.
def Live (k : ℕ) (s : Finset W) : Prop :=
  ∀ P : ℕ → Finset W → Prop, P 0 {goal} →
    (∀ {n v}, P n v → P (n+1) v) →
    (∀ {n r a b} (q : Bool), a ≠ b → valOf q a b ∉ insert a (insert b r) →
      P n (insert (valOf q a b) r) → P (n + charge q a b) (insert a (insert b r))) → P k s

namespace Live

theorem done : Live 0 {goal} := fun _ base _ _ => base

theorem pad {k s} (h : Live k s) : Live (k+1) s :=
  fun P base grow join => grow (h P base grow join)

theorem step {k r a b} (q : Bool) (hne : a ≠ b)
    (hn : valOf q a b ∉ insert a (insert b r)) (h : Live k (insert (valOf q a b) r)) :
    Live (k + charge q a b) (insert a (insert b r)) :=
  fun P base grow join => join q hne hn (h P base grow join)

theorem induct
    {motive : (k : ℕ) → (s : Finset W) → Live k s → Prop}
    (done : motive 0 {goal} Live.done)
    (pad : ∀ {k s} (h : Live k s), motive k s h → motive (k+1) s (Live.pad h))
    (step : ∀ {k r a b} (q : Bool) (hne : a ≠ b) (hn : valOf q a b ∉ insert a (insert b r))
      (h : Live k (insert (valOf q a b) r)), motive k _ h →
      motive (k + charge q a b) (insert a (insert b r)) (Live.step q hne hn h))
    {k s} (h : Live k s) : motive k s h := by
  apply (show (∃ e : Live k s, motive k s e) → motive k s h from fun ⟨_,w⟩ => w)
  apply h (fun n v => ∃ e : Live n v, motive n v e)
  · exact ⟨Live.done,done⟩
  · rintro n v ⟨e, ih⟩; exact ⟨Live.pad e,pad e ih⟩
  · rintro n r a b q hne hn ⟨e, ih⟩
    exact ⟨Live.step q hne hn e,step q hne hn e ih⟩

end Live



theorem live_weaken {k l s} (hle : k ≤ l) (h : Live k s) : Live l s := by
  induction hle with
  | refl => exact h
  | step _ ih => exact .pad ih

theorem compression {k s} (h : Build k s) : ∃ t ⊆ s, Live k t := by
  induction h using Build.induct with
  | done hg => exact ⟨{goal}, Finset.singleton_subset_iff.mpr hg, .done⟩
  | pad _ ih =>
    obtain ⟨t, hs, ht⟩ := ih
    exact ⟨t, hs, .pad ht⟩
  | @step k s a b ha hb hne q _ ih =>
    obtain ⟨t, ht, hrun⟩ := ih
    let z := valOf q a b
    by_cases sub : t ⊆ s
    · exact ⟨t, sub, live_weaken (by omega) hrun⟩
    have hzmem : z ∈ t := by
      by_contra hn
      apply sub
      intro u hu
      rcases Finset.mem_insert.mp (ht hu) with rfl | hh
      · exact False.elim (hn hu)
      · exact hh
    have hzout : z ∉ s := by
      intro hz
      exact sub ((Finset.insert_eq_of_mem hz) ▸ ht)
    let rest := t.erase z
    have hr : rest ⊆ s := by
      intro u hu
      obtain ⟨hne, hin⟩ := Finset.mem_erase.mp hu
      exact (Finset.mem_insert.mp (ht hin)).resolve_left hne
    have hs : insert a (insert b rest) ⊆ s := Finset.insert_subset ha (Finset.insert_subset hb hr)
    refine ⟨_, hs, .step q hne (fun hz => hzout (hs hz)) ?_⟩
    simpa [rest, z, Finset.insert_erase hzmem] using hrun

theorem live_card {k s} (h : Live k s) : s.card ≤ k+1 := by
  induction h using Live.induct with
  | done => simp
  | pad _ ih => omega
  | @step k r a b q _ hn _ ih =>
    have hz : valOf q a b ∉ r := fun hm => hn (by simp [hm])
    rw [Finset.card_insert_of_notMem hz] at ih
    have h1 := Finset.card_insert_le a (insert b r)
    have h2 := Finset.card_insert_le b r
    have h3 := charge_pos q a b
    omega

theorem live_separates (D : W → Prop) (hg : D goal)
    (hop : ∀ q a b, D (valOf q a b) → D a ∨ D b) {k s} (h : Live k s) : ∃ w ∈ s, D w := by
  induction h using Live.induct with
  | done => exact ⟨goal, by simp, hg⟩
  | pad _ ih => exact ih
  | @step k r a b q _ _ _ ih =>
    obtain ⟨w, hw, hd⟩ := ih
    rcases Finset.mem_insert.mp hw with rfl | hw
    · rcases hop q a b hd with hh | hh
      · exact ⟨a, by simp, hh⟩
      · exact ⟨b, by simp, hh⟩
    · exact ⟨w, by simp [hw], hd⟩


def ops (x y : W) : List W := [x &&& y, x ||| y]

def sep (x : W) : BitVec 54 := ((x >>> 54) &&& ~~~x).setWidth 54

def cuts (ws : List W) : BitVec 54 := ws.foldr (fun w v => sep w ||| v) 0

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) := (ops a b).toFinset

def differs (i : Fin 54) (w : W) : Prop :=
  w.getLsbD (54 + i.val) = true ∧ w.getLsbD i.val = false

theorem ops_differs (i : Fin 54) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  unfold differs at hd ⊢
  rcases hz with rfl | rfl <;> revert hd <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or] <;>
    cases a.getLsbD (54 + i.val) <;> cases a.getLsbD i.val <;>
    cases b.getLsbD (54 + i.val) <;> cases b.getLsbD i.val <;> simp

theorem goal_differs : ∀ i : Fin 54, differs i goal := by
  unfold differs
  decide

theorem cuts_spec (ws : List W) (i : Fin 54) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have hi : i.val < 108 := by omega
    simp [sep, i.isLt, differs, hi, Nat.add_comm]


theorem value_diff (i : Fin 54) (q : Bool) (a b : W) (h : differs i (valOf q a b)) :
    differs i a ∨ differs i b :=
  ops_differs i a b (valOf q a b) (by cases q <;> simp [basicOps, ops, valOf]) h

theorem cuts_full {k : ℕ} {ws : List W} (h : Live k ws.toFinset) :
    cuts ws = -1 := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (goal_differs ⟨j, hj⟩) (value_diff ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 54)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) :
    ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

theorem full_inputs {s : Finset W} {k : ℕ} (hs : s ⊆ inputs.toFinset)
    (hr : Live k s) : s = inputs.toFinset := by
  apply Finset.Subset.antisymm hs
  intro a ha
  let sites : List (Fin 54) := [1, 0, 9, 27, 36]
  have necessary : inputs.all (fun a => sites.any (fun i => inputs.all (fun b =>
      !(b.getLsbD (54 + i.val) && !b.getLsbD i.val) || b == a))) = true := by decide
  obtain ⟨i, _, hAll⟩ :=
    List.any_eq_true.mp (List.all_eq_true.mp necessary a (List.mem_toFinset.mp ha))
  have hi (b : W) (hb : b ∈ inputs) (hd : differs i b) : b = a := by
    have hrow := List.all_eq_true.mp hAll b hb
    obtain ⟨h1, h2⟩ := hd
    simpa [h1, h2] using hrow
  obtain ⟨b, hb, hd⟩ := live_separates (differs i) (goal_differs i) (value_diff i) hr
  exact hi b (List.mem_toFinset.mp (hs hb)) hd ▸ hb



def fastWide (w : W) : Bool :=
  let m := w.setWidth 5
  (m &&& (m - 1)) != 0

theorem fastWide_eq (w : W) : fastWide w = isWide w := by
  have h : ∀ m : BitVec 5, ((m &&& (m - 1)) != 0) =
      decide (∃ u v : Fin 5, u ≠ v ∧ m.getLsbD u.val = true ∧ m.getLsbD v.val = true) := by
    decide +kernel
  rw [fastWide, h]
  simp [isWide, wide, Fin.is_lt]

def fastCharge (q : Bool) (a b : W) : ℕ :=
  if q then if fastWide (a ||| b) then 1 else 2 else 1

theorem fastCharge_eq (q : Bool) (a b : W) : fastCharge q a b = charge q a b := by
  simp [fastCharge, charge, orWeight, fastWide_eq]

def dispatchW (budget : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  [false,true].any fun q =>
    let w := valOf q a b
    let c := fastCharge q a b
    let rem := budget-c
    (c ≤ budget) && !((a::b::r).contains w) &&
      (keepChoices a b r).any fun kept =>
        (kept.length ≤ rem) && (cuts (w :: kept) == -1) && next rem (w :: kept)

def explore : ℕ → ℕ → List W → Bool
  | 0, _, ws => ws == [goal]
  | n+1, budget, ws => ws == [goal] ||
    (pairs ws).any (fun (a,b,r) => dispatchW budget (explore n) a b r)

theorem explore_complete {k s} (h : Live k s) {fuel budget : ℕ} {ws : List W}
    (hb : k ≤ budget) (hf : budget ≤ fuel) (hs : ws.toFinset=s) (hn : ws.Nodup) :
    explore fuel budget ws = true := by
  induction h using Live.induct generalizing ws fuel budget with
  | done =>
    have hh := singleton_list hn hs
    cases fuel <;> simp [explore, hh]
  | pad h ih => exact ih (by omega) hf hs hn
  | @step k rest a b q hab hz htail ih =>
    have cpos := charge_pos q a b
    cases fuel with
    | zero => omega
    | succ fuel =>
      have ha : a ∈ ws := List.mem_toFinset.mp (hs ▸ by simp)
      have hb' : b ∈ ws := List.mem_toFinset.mp (hs ▸ by simp)
      obtain ⟨r, hm, hp⟩ := pick_two ha hb' hab
      have go {x y : W} (perm : ws.Perm (x :: y :: r))
          (hset : ws.toFinset=insert x (insert y rest))
          (hv : valOf q x y=valOf q a b) (hc : charge q x y=charge q a b) :
          dispatchW budget (explore fuel) x y r = true := by
        obtain ⟨kept, hk, hkn, hke⟩ := recover_kept perm hn hset
        have fresh : valOf q a b ∉ ws := by
          intro hin
          exact hz (hs ▸ (List.mem_toFinset.mpr hin))
        have hnot : valOf q a b ∉ x :: y :: r := fun hin => fresh (perm.mem_iff.mpr hin)
        have hnxt : (valOf q a b :: kept).Nodup := List.nodup_cons.mpr ⟨by
          intro hin
          apply hz
          have hh : valOf q a b ∈ rest := hke ▸ List.mem_toFinset.mpr hin
          simp [hh], hkn⟩
        have hns : (valOf q a b :: kept).toFinset = insert (valOf q a b) rest := by simp [hke]
        have hcard := live_card htail
        rw [←hns,List.toFinset_card_of_nodup hnxt,List.length_cons] at hcard
        have hcuts := cuts_full (hns.symm ▸ htail)
        have hrec : explore fuel (budget-charge q a b) (valOf q a b :: kept) = true :=
          ih (by omega) (by omega) hns hnxt
        apply List.any_eq_true.mpr
        refine ⟨q, by cases q <;> simp, ?_⟩
        dsimp only
        rw [fastCharge_eq, hv, hc]
        have hconst : (x :: y :: r).contains (valOf q a b) = false := by
          cases hh : (x :: y :: r).contains (valOf q a b) with
          | false => rfl
          | true => exact False.elim (hnot (List.contains_iff_mem.mp hh))
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
        refine ⟨⟨by omega, hconst⟩, List.any_eq_true.mpr ⟨kept, hk, ?_⟩⟩
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
        exact ⟨⟨by omega, hcuts⟩, hrec⟩
      simp only [explore, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a,b,r), direct, go hp hs rfl rfl⟩
      · exact ⟨(b,a,r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm])
          (swap_val q a b) (swap_charge q a b)⟩

theorem cover_step {n budget : ℕ} {ws : List W} {states : List (ℕ × List W)}
    (hc : (ws == [goal] || (pairs ws).any (fun (a,b,r) =>
      dispatchW budget (fun k s => !states.contains (k,s)) a b r)) = false)
    (ht : states.all (fun s => !(explore n s.1 s.2)) = true) :
    explore (n+1) budget ws = false := by
  have transfer (a b : W) (r : List W) (hd : dispatchW budget (explore n) a b r = true) :
      dispatchW budget (fun k s => !states.contains (k,s)) a b r = true := by
    simp only [dispatchW, List.any_eq_true, Bool.and_eq_true] at hd ⊢
    obtain ⟨q, hq, hcost, kept, hk, hgood, hnext⟩ := hd
    refine ⟨q, hq, hcost, kept, hk, hgood, ?_⟩
    cases hmem : states.contains (budget - fastCharge q a b, valOf q a b :: kept) with
    | false => rfl
    | true =>
      have hfor := List.all_eq_true.mp ht _ (List.contains_iff_mem.mp hmem)
      simp [hnext] at hfor
  cases he : explore (n+1) budget ws with
  | false => rfl
  | true =>
    simp only [explore, Bool.or_eq_true, List.any_eq_true] at he
    have contrad : (ws == [goal] || (pairs ws).any (fun (a,b,r) =>
        dispatchW budget (fun k s => !states.contains (k,s)) a b r)) = true := by
      simp only [Bool.or_eq_true, List.any_eq_true]
      rcases he with e | ⟨⟨a,b,r⟩, hm, hd⟩
      · exact Or.inl e
      · exact Or.inr ⟨(a,b,r),hm,transfer a b r hd⟩
    rw [hc] at contrad
    contradiction

end PEqualNP.Outside.L_meta_700_aux

-- Search core declarations are provided by the assembled file.
namespace PEqualNP.Outside.L_meta_700_aux

abbrev Item := Bool × W × W
def Item.left (g : Item) := g.2.1
def Item.right (g : Item) := g.2.2
def Item.out (g : Item) := valOf g.1 g.left g.right
def Item.wt (g : Item) := charge g.1 g.left g.right
def amount (t : List Item) := (t.map Item.wt).sum

def Run : List Item → Finset W → Prop
  | [],s => goal ∈ s
  | g::t,s => g.left ∈ s ∧ g.right ∈ s ∧ g.left ≠ g.right ∧ Run t (insert g.out s)

def Active : List Item → Finset W → Prop
  | [],s => s = {goal}
  | g::t,s => ∃ r, s = insert g.left (insert g.right r) ∧ g.left ≠ g.right ∧
      g.out ∉ s ∧ Active t (insert g.out r)

theorem has_run {k s} (h : Build k s) : ∃ t, Run t s ∧ amount t ≤ k := by
  induction h using Build.induct with
  | done hg => exact ⟨[],hg,by simp [amount]⟩
  | pad _ ih => obtain ⟨t,hr,hk⟩ := ih; exact ⟨t,hr,by omega⟩
  | @step k s a b ha hb hn q _ ih =>
    obtain ⟨t,hr,hk⟩ := ih
    refine ⟨(q,a,b)::t, ⟨ha,hb,hn,hr⟩, ?_⟩
    change charge q a b + amount t ≤ k + charge q a b
    omega

theorem active_live {t : List Item} {s} (h : Active t s) : Live (amount t) s := by
  induction t generalizing s with
  | nil => change s = {goal} at h; rw [h]; exact .done
  | cons g t ih =>
    obtain ⟨r,rfl,hn,hfresh,ht⟩ := h
    change Live (g.wt+amount t) _
    rw [Nat.add_comm]
    exact .step g.1 hn hfresh (ih ht)

theorem active_run {t : List Item} {s v} (h : Active t s) (hs : s ⊆ v) : Run t v := by
  induction t generalizing s v with
  | nil => change s = {goal} at h; exact hs (h ▸ by simp)
  | cons g t ih =>
    obtain ⟨r,rfl,hn,hfresh,ht⟩ := h
    refine ⟨hs (by simp),hs (by simp),hn,ih ht ?_⟩
    exact Finset.insert_subset_insert _ (fun a ha => hs (by simp [ha]))

theorem compress_run {gs : List Item} {s} (h : Run gs s) :
    ∃ v ⊆ s, ∃ t : List Item, t.Sublist gs ∧ Active t v := by
  induction gs generalizing s with
  | nil => exact ⟨{goal},Finset.singleton_subset_iff.mpr h,[],.slnil,rfl⟩
  | cons g gs ih =>
    obtain ⟨ha,hb,hab,hh⟩ := h
    obtain ⟨v,hv,t,hsub,hr⟩ := ih hh
    by_cases hs : v ⊆ s
    · exact ⟨v,hs,t,.cons _ hsub,hr⟩
    have hg : g.out ∈ v := by
      by_contra hnot
      apply hs
      intro a ha
      rcases Finset.mem_insert.mp (hv ha) with rfl | h
      · exact False.elim (hnot ha)
      · exact h
    have hnew : g.out ∉ s := fun hz => hs ((Finset.insert_eq_of_mem hz) ▸ hv)
    let r := v.erase g.out
    have hrsub : r ⊆ s := by
      intro a ha
      obtain ⟨hneq,hmem⟩ := Finset.mem_erase.mp ha
      exact (Finset.mem_insert.mp (hv hmem)).resolve_left hneq
    have hsub' := Finset.insert_subset ha (Finset.insert_subset hb hrsub)
    refine ⟨_,hsub',g::t,.cons_cons _ hsub,r,rfl,hab,fun hz => hnew (hsub' hz),?_⟩
    simpa [r,Finset.insert_erase hg] using hr

def inversions : List Item → ℕ
  | [] => 0
  | g::t => t.countP (fun h => h.out.toNat < g.out.toNat) + inversions t

theorem inv_sub {s t : List Item} (h : s.Sublist t) : inversions s ≤ inversions t := by
  induction h with
  | slnil => rfl
  | cons a h ih => simp only [inversions]; omega
  | cons_cons a h ih =>
    simp only [inversions]
    exact Nat.add_le_add h.countP_le ih

theorem inv_swap (p : List Item) (a b : Item) (t : List Item)
    (hd : b.out.toNat < a.out.toNat) :
    inversions (p ++ b::a::t) + 1 = inversions (p ++ a::b::t) := by
  induction p with
  | nil =>
    have hanti : ¬a.out.toNat < b.out.toNat := by omega
    simp [inversions, hd, hanti]; omega
  | cons g p ih =>
    simp only [List.cons_append,inversions]
    have hc : (p ++ b::a::t).countP (fun h => h.out.toNat < g.out.toNat) =
        (p ++ a::b::t).countP (fun h => h.out.toNat < g.out.toNat) := by
      apply List.Perm.countP_eq
      exact List.Perm.append_left p (.swap _ _ _)
    omega

theorem swap_run (p : List Item) (a b : Item) (t : List Item) {s}
    (hr : Run (p ++ a::b::t) s) (hl : b.left ≠ a.out) (hj : b.right ≠ a.out) :
    Run (p ++ b::a::t) s := by
  induction p generalizing s with
  | nil =>
    obtain ⟨hal,har,han,hbl,hbr,hbn,hrest⟩ := hr
    exact ⟨(Finset.mem_insert.mp hbl).resolve_left hl,(Finset.mem_insert.mp hbr).resolve_left hj,hbn,
      Finset.mem_insert_of_mem hal,Finset.mem_insert_of_mem har,han,by
        simpa only [Finset.insert_comm a.out b.out] using hrest⟩
  | cons g p ih =>
    obtain ⟨hl,hr,hn,ht⟩:=hr
    exact ⟨hl,hr,hn,ih ht⟩

def canonOrder (t : List Item) : Prop := ∀ p a b s, t=p++a::b::s →
    b.left=a.out ∨ b.right=a.out ∨ a.out.toNat≤b.out.toNat

theorem canon_exists {k : ℕ} (hb : Build k inputs.toFinset) :
    ∃ t, Active t inputs.toFinset ∧ amount t ≤ k ∧ canonOrder t := by
  classical
  obtain ⟨t,hr,hk⟩ := has_run hb
  let P := fun m : ℕ => ∃ t : List Item, Run t inputs.toFinset ∧ amount t≤k ∧
      t.length + inversions t=m
  have hex : ∃m,P m := ⟨_,t,hr,hk,rfl⟩
  obtain ⟨u,hu,huk,huv⟩ := Nat.find_spec hex
  have best (v : List Item) (hv : Run v inputs.toFinset) (vk : amount v ≤ k) :
      u.length+inversions u ≤ v.length+inversions v := by
    rw [huv]
    exact Nat.find_min' hex ⟨v,hv,vk,rfl⟩
  obtain ⟨v,hsub,w,hwu,hw⟩ := compress_run hu
  have hsv := full_inputs hsub (active_live hw)
  subst v
  have wrun := active_run hw (Finset.Subset.refl _)
  have cost : amount w ≤ k := by
    apply le_trans _ huk
    exact List.Sublist.sum_le_sum (hwu.map Item.wt) (fun _ _ => Nat.zero_le _)
  have lv := hwu.length_le
  have iv := inv_sub hwu
  have min := best w wrun cost
  have same : w=u := hwu.eq_of_length (by omega)
  subst w
  refine ⟨u,hw,huk,?_⟩
  intro p a b tail he
  by_contra! bad
  subst u
  have alt := swap_run p a b tail hu bad.1 bad.2.1
  have chargeEq : amount (p++b::a::tail) = amount (p++a::b::tail) := by
    simp [amount,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]
  have hh := best _ alt (chargeEq ▸ huk)
  have hi := inv_swap p a b tail bad.2.2
  simp only [List.length_append,List.length_cons] at hh
  omega
end PEqualNP.Outside.L_meta_700_aux

namespace PEqualNP.Outside.L_meta_700_aux

def allowed (p a b w : W) : Bool := (a == p) || (b == p) || (p.toNat ≤ w.toNat)

def dispatchO (p : W) (budget : ℕ) (next : ℕ → W → List W → Bool)
    (a b : W) (r : List W) : Bool :=
  [false,true].any fun q =>
    let w := valOf q a b
    let c := fastCharge q a b
    let rem := budget-c
    allowed p a b w && (c ≤ budget) && !((a::b::r).contains w) &&
      (keepChoices a b r).any fun kept =>
        (kept.length ≤ rem) && (cuts (w :: kept) == -1) && next rem w (w :: kept)

def orderSearch : ℕ → ℕ → W → List W → Bool
  | 0, _, _, ws => ws == [goal]
  | n+1, budget, p, ws => ws == [goal] ||
    (pairs ws).any (fun (a,b,r) => dispatchO p budget (orderSearch n) a b r)

def atHead (p : W) : List Item → Prop
  | [] => True
  | g::_ => g.left=p ∨ g.right=p ∨ p.toNat≤g.out.toNat

theorem zero_head (t : List Item) : atHead 0 t := by
  cases t with
  | nil => trivial
  | cons x t => exact Or.inr (.inr (Nat.zero_le _))

theorem canon_tail {g : Item} {t : List Item} (h : canonOrder (g::t)) : canonOrder t := by
  intro p a b s he
  exact h (g::p) a b s (by simp [he])

theorem canon_head {g : Item} {t : List Item} (h : canonOrder (g::t)) : atHead g.out t := by
  cases t with
  | nil => trivial
  | cons b s => exact h [] g b s rfl

theorem order_complete {t : List Item} {s} (h : Active t s) (ho : canonOrder t)
    {fuel budget : ℕ} {p : W} {ws : List W}
    (hh : atHead p t) (hb : amount t ≤ budget) (hf : budget ≤ fuel) (hs : ws.toFinset=s)
    (hn : ws.Nodup) : orderSearch fuel budget p ws = true := by
  induction t generalizing s ws p fuel budget with
  | nil =>
    change s={goal} at h
    have hg := singleton_list hn (hs.trans h)
    cases fuel <;> simp [orderSearch,hg]
  | cons g t ih =>
    obtain ⟨rest,hset,hab,hz,htail⟩ := h
    rw [hset] at hs hz
    have cpos := charge_pos g.1 g.left g.right
    have cost : amount t + charge g.1 g.left g.right ≤ budget := by
      change g.wt + amount t ≤ budget at hb
      change amount t + g.wt ≤ budget
      omega
    cases fuel with
    | zero => omega
    | succ fuel =>
      have ha : g.left ∈ ws := List.mem_toFinset.mp (hs ▸ by simp)
      have hb' : g.right ∈ ws := List.mem_toFinset.mp (hs ▸ by simp)
      obtain ⟨r, hm, hp⟩ := pick_two ha hb' hab
      have go {x y : W} (perm : ws.Perm (x :: y :: r))
          (hset : ws.toFinset=insert x (insert y rest))
          (hv : valOf g.1 x y=g.out) (hc : charge g.1 x y=g.wt)
          (al : x=p ∨ y=p ∨ p.toNat≤g.out.toNat) :
          dispatchO p budget (orderSearch fuel) x y r = true := by
        obtain ⟨kept, hk, hkn, hke⟩ := recover_kept perm hn hset
        have fresh : g.out ∉ ws := fun hin => hz (hs ▸ List.mem_toFinset.mpr hin)
        have hnot : g.out ∉ x :: y :: r := fun hin => fresh (perm.mem_iff.mpr hin)
        have hnd : (g.out :: kept).Nodup := List.nodup_cons.mpr ⟨by
          intro hin
          apply hz
          have hh' : g.out ∈ rest := hke ▸ List.mem_toFinset.mpr hin
          simp [hh'], hkn⟩
        have hns : (g.out :: kept).toFinset = insert g.out rest := by simp [hke]
        have htail' := active_live htail
        have hcard := live_card htail'
        rw [←hns,List.toFinset_card_of_nodup hnd,List.length_cons] at hcard
        have hcuts := cuts_full (hns.symm ▸ htail')
        have hfuel' : budget-g.wt ≤ fuel := by change budget-charge g.1 g.left g.right≤fuel; omega
        have hrec : orderSearch fuel (budget-g.wt) g.out (g.out::kept) = true :=
          ih htail (canon_tail ho) (canon_head ho) (by change amount t≤budget-charge g.1 g.left g.right; omega) hfuel' hns hnd
        apply List.any_eq_true.mpr
        refine ⟨g.1, by cases g.1 <;> simp, ?_⟩
        dsimp only
        rw [fastCharge_eq,hv,hc]
        have hconst : (x :: y :: r).contains g.out = false := by
          cases hw : (x :: y :: r).contains g.out with
          | false => rfl
          | true => exact False.elim (hnot (List.contains_iff_mem.mp hw))
        have allow : allowed p x y g.out = true := by
          simp only [allowed, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
          tauto
        have hwt : g.wt ≤ budget := by change charge g.1 g.left g.right≤budget; omega
        simp only [allow,Bool.true_and,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true']
        refine ⟨⟨hwt,hconst⟩,List.any_eq_true.mpr ⟨kept,hk,?_⟩⟩
        simp only [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq]
        exact ⟨⟨by change kept.length≤budget-charge g.1 g.left g.right; omega,hcuts⟩,hrec⟩
      simp only [orderSearch,Bool.or_eq_true,List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(g.left,g.right,r),direct,go hp hs rfl rfl hh⟩
      · exact ⟨(g.right,g.left,r),swap,go (hp.trans (.swap _ _ _)) (by rw [hs,Finset.insert_comm])
          (swap_val g.1 g.left g.right) (swap_charge g.1 g.left g.right)
          (by change g.left=p ∨ g.right=p ∨ _ at hh; tauto)⟩

theorem ocover_step {n budget : ℕ} {ws : List W} {p : W} {states : List (ℕ × W × List W)}
    (hc : (ws == [goal] || (pairs ws).any (fun (a,b,r) =>
      dispatchO p budget (fun k x s => !states.contains (k,x,s)) a b r)) = false)
    (ht : states.all (fun s => !(orderSearch n s.1 s.2.1 s.2.2)) = true) :
    orderSearch (n+1) budget p ws = false := by
  have transfer (a b : W) (r : List W) (hd : dispatchO p budget (orderSearch n) a b r = true) :
      dispatchO p budget (fun k x s => !states.contains (k,x,s)) a b r = true := by
    simp only [dispatchO, List.any_eq_true, Bool.and_eq_true] at hd ⊢
    obtain ⟨q,hq,hcost,kept,hk,hgood,hnext⟩ := hd
    refine ⟨q,hq,hcost,kept,hk,hgood,?_⟩
    cases hmem : states.contains (budget - fastCharge q a b,valOf q a b,valOf q a b :: kept) with
    | false => rfl
    | true =>
      have hfor := List.all_eq_true.mp ht _ (List.contains_iff_mem.mp hmem)
      simp [hnext] at hfor
  cases he : orderSearch (n+1) budget p ws with
  | false => rfl
  | true =>
    simp only [orderSearch,Bool.or_eq_true,List.any_eq_true] at he
    have contrad : (ws == [goal] || (pairs ws).any (fun (a,b,r) =>
        dispatchO p budget (fun k x s => !states.contains (k,x,s)) a b r)) = true := by
      simp only [Bool.or_eq_true,List.any_eq_true]
      rcases he with e | ⟨⟨a,b,r⟩, hm, hd⟩
      · exact .inl e
      · exact .inr ⟨(a,b,r),hm,transfer a b r hd⟩
    rw [hc] at contrad
    contradiction

end PEqualNP.Outside.L_meta_700_aux

namespace PEqualNP.Outside.L_meta_700_aux
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord0 : orderSearch 7 7 0 [0,2417842429535473200466308,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord1 : orderSearch 7 7 0 [0,9205357638345293824,2417842429535473200466308,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord2 : orderSearch 7 6 2417851634893111545760132 [2417851634893111545760132,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord3 : orderSearch 7 6 2417851634893111545760132 [2417851634893111545760132,9205357638345293824,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord4 : orderSearch 7 6 2417851634893111545760132 [2417851634893111545760132,2417842429535473200466308,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord5 : orderSearch 7 6 2417851634893111545760132 [2417851634893111545760132,9205357638345293824,2417842429535473200466308,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord6 : orderSearch 7 7 0 [0,323885963880500264155966194405544,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord7 : orderSearch 7 7 0 [0,9205357638345293824,323885963880500264155966194405544,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord8 : orderSearch 7 6 323885963880509469513604539699368 [323885963880509469513604539699368,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord9 : orderSearch 7 6 323885963880509469513604539699368 [323885963880509469513604539699368,9205357638345293824,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord10 : orderSearch 7 6 323885963880509469513604539699368 [323885963880509469513604539699368,323885963880500264155966194405544,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord11 : orderSearch 7 6 323885963880509469513604539699368 [323885963880509469513604539699368,9205357638345293824,323885963880500264155966194405544,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord12 : orderSearch 7 7 0 [0,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord13 : orderSearch 7 7 0 [0,9205357638345293824,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord14 : orderSearch 7 6 324517315718396658605603418186064 [324517315718396658605603418186064,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord15 : orderSearch 7 6 324517315718396658605603418186064 [324517315718396658605603418186064,9205357638345293824,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord16 : orderSearch 7 6 324517315718396658605603418186064 [324517315718396658605603418186064,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord17 : orderSearch 7 6 324517315718396658605603418186064 [324517315718396658605603418186064,9205357638345293824,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord18 : orderSearch 7 7 633825300114100176419220670051 [633825300114100176419220670051,633822886984823975214363968001,9205357638345293824,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord19 : orderSearch 7 7 633825300114100176419220670051 [633825300114100176419220670051,633822886984823975214363968001,2413138481558843201995874,9205357638345293824,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord20 : orderSearch 7 7 4713143110832790437888 [4713143110832790437888,633822886984823975214363968001,2417842429535473200466308,9205357638345293824,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord21 : orderSearch 7 7 633825300114110399854773996421 [633825300114110399854773996421,633822886984823975214363968001,2417842429535473200466308,9205357638345293824,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord22 : orderSearch 7 7 1235522187646151016549711872 [1235522187646151016549711872,633822886984823975214363968001,323885963880500264155966194405544,9205357638345293824,2413138481558843201995874,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord23 : orderSearch 7 7 324518551245297441980164008661673 [324518551245297441980164008661673,633822886984823975214363968001,323885963880500264155966194405544,9205357638345293824,2413138481558843201995874,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord24 : orderSearch 7 7 632587360074829320473452478464 [632587360074829320473452478464,633822886984823975214363968001,324517315718387453247965072892240,9205357638345293824,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord25 : orderSearch 7 7 324518551245297447902705984381777 [324518551245297447902705984381777,633822886984823975214363968001,324517315718387453247965072892240,9205357638345293824,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord26 : orderSearch 7 7 2413129272746388704198656 [2413129272746388704198656,2417842429535473200466308,9205357638345293824,633822886984823975214363968001,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord27 : orderSearch 7 7 2413129272746388704198656 [2413129272746388704198656,2413138481558843201995874,2417842429535473200466308,9205357638345293824,633822886984823975214363968001,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord28 : orderSearch 7 7 2417851638347927698263526 [2417851638347927698263526,2413138481558843201995874,2417842429535473200466308,9205357638345293824,633822886984823975214363968001,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord29 : orderSearch 7 7 323885966293638744586706162930922 [323885966293638744586706162930922,2413138481558843201995874,323885963880500264155966194405544,9205357638345293824,633822886984823975214363968001,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord30 : orderSearch 7 7 324517318131525932550601807947122 [324517318131525932550601807947122,2413138481558843201995874,324517315718387453247965072892240,9205357638345293824,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord31 : orderSearch 7 7 323885966298342689179026460989868 [323885966298342689179026460989868,2417842429535473200466308,323885963880500264155966194405544,9205357638345293824,633822886984823975214363968001,2413138481558843201995874,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord32 : orderSearch 7 7 324517318136229873758612405594580 [324517318136229873758612405594580,2417842429535473200466308,324517315718387453247965072892240,9205357638345293824,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord33 : orderSearch 7 7 323884728358312612082407668973568 [323884728358312612082407668973568,323885963880500264155966194405544,324517315718387453247965072892240,9205357638345293824,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord34 : orderSearch 7 7 324518551240575105321523598324216 [324518551240575105321523598324216,323885963880500264155966194405544,324517315718387453247965072892240,9205357638345293824,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord35 : orderSearch 8 8 9205357638345293824 [9205357638345293824,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  apply ocover_step (states := [(7,0,[0,2417842429535473200466308,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240]),(7,0,[0,9205357638345293824,2417842429535473200466308,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240]),(6,2417851634893111545760132,[2417851634893111545760132,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240]),(6,2417851634893111545760132,[2417851634893111545760132,9205357638345293824,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240]),(6,2417851634893111545760132,[2417851634893111545760132,2417842429535473200466308,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240]),(6,2417851634893111545760132,[2417851634893111545760132,9205357638345293824,2417842429535473200466308,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240]),(7,0,[0,323885963880500264155966194405544,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,324517315718387453247965072892240]),(7,0,[0,9205357638345293824,323885963880500264155966194405544,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,324517315718387453247965072892240]),(6,323885963880509469513604539699368,[323885963880509469513604539699368,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,324517315718387453247965072892240]),(6,323885963880509469513604539699368,[323885963880509469513604539699368,9205357638345293824,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,324517315718387453247965072892240]),(6,323885963880509469513604539699368,[323885963880509469513604539699368,323885963880500264155966194405544,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,324517315718387453247965072892240]),(6,323885963880509469513604539699368,[323885963880509469513604539699368,9205357638345293824,323885963880500264155966194405544,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,324517315718387453247965072892240]),(7,0,[0,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544]),(7,0,[0,9205357638345293824,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544]),(6,324517315718396658605603418186064,[324517315718396658605603418186064,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544]),(6,324517315718396658605603418186064,[324517315718396658605603418186064,9205357638345293824,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544]),(6,324517315718396658605603418186064,[324517315718396658605603418186064,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544]),(6,324517315718396658605603418186064,[324517315718396658605603418186064,9205357638345293824,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544]),(7,633825300114100176419220670051,[633825300114100176419220670051,633822886984823975214363968001,9205357638345293824,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240]),(7,633825300114100176419220670051,[633825300114100176419220670051,633822886984823975214363968001,2413138481558843201995874,9205357638345293824,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240]),(7,4713143110832790437888,[4713143110832790437888,633822886984823975214363968001,2417842429535473200466308,9205357638345293824,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240]),(7,633825300114110399854773996421,[633825300114110399854773996421,633822886984823975214363968001,2417842429535473200466308,9205357638345293824,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240]),(7,1235522187646151016549711872,[1235522187646151016549711872,633822886984823975214363968001,323885963880500264155966194405544,9205357638345293824,2413138481558843201995874,2417842429535473200466308,324517315718387453247965072892240]),(7,324518551245297441980164008661673,[324518551245297441980164008661673,633822886984823975214363968001,323885963880500264155966194405544,9205357638345293824,2413138481558843201995874,2417842429535473200466308,324517315718387453247965072892240]),(7,632587360074829320473452478464,[632587360074829320473452478464,633822886984823975214363968001,324517315718387453247965072892240,9205357638345293824,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544]),(7,324518551245297447902705984381777,[324518551245297447902705984381777,633822886984823975214363968001,324517315718387453247965072892240,9205357638345293824,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544]),(7,2413129272746388704198656,[2413129272746388704198656,2417842429535473200466308,9205357638345293824,633822886984823975214363968001,323885963880500264155966194405544,324517315718387453247965072892240]),(7,2413129272746388704198656,[2413129272746388704198656,2413138481558843201995874,2417842429535473200466308,9205357638345293824,633822886984823975214363968001,323885963880500264155966194405544,324517315718387453247965072892240]),(7,2417851638347927698263526,[2417851638347927698263526,2413138481558843201995874,2417842429535473200466308,9205357638345293824,633822886984823975214363968001,323885963880500264155966194405544,324517315718387453247965072892240]),(7,323885966293638744586706162930922,[323885966293638744586706162930922,2413138481558843201995874,323885963880500264155966194405544,9205357638345293824,633822886984823975214363968001,2417842429535473200466308,324517315718387453247965072892240]),(7,324517318131525932550601807947122,[324517318131525932550601807947122,2413138481558843201995874,324517315718387453247965072892240,9205357638345293824,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544]),(7,323885966298342689179026460989868,[323885966298342689179026460989868,2417842429535473200466308,323885963880500264155966194405544,9205357638345293824,633822886984823975214363968001,2413138481558843201995874,324517315718387453247965072892240]),(7,324517318136229873758612405594580,[324517318136229873758612405594580,2417842429535473200466308,324517315718387453247965072892240,9205357638345293824,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544]),(7,323884728358312612082407668973568,[323884728358312612082407668973568,323885963880500264155966194405544,324517315718387453247965072892240,9205357638345293824,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308]),(7,324518551240575105321523598324216,[324518551240575105321523598324216,323885963880500264155966194405544,324517315718387453247965072892240,9205357638345293824,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308])])
  · decide +kernel
  · simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.not_false, ord0, ord1, ord2, ord3, ord4, ord5, ord6, ord7, ord8, ord9, ord10, ord11, ord12, ord13, ord14, ord15, ord16, ord17, ord18, ord19, ord20, ord21, ord22, ord23, ord24, ord25, ord26, ord27, ord28, ord29, ord30, ord31, ord32, ord33, ord34]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord36 : orderSearch 6 6 4713143110832790437888 [4713143110832790437888,2417842415857221494636544,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord37 : orderSearch 6 5 633825300114096721603068166657 [633825300114096721603068166657,2417842415857221494636544,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord38 : orderSearch 6 5 633825300114096721603068166657 [633825300114096721603068166657,2417842415857221494636544,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord39 : orderSearch 6 6 2413129272746388704198656 [2413129272746388704198656,2417842415857221494636544,2413138481558843201995874,633822886984823975214363968001,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord40 : orderSearch 6 5 2417851624669675992433762 [2417851624669675992433762,2417842415857221494636544,633822886984823975214363968001,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord41 : orderSearch 6 5 2417851624669675992433762 [2417851624669675992433762,2417842415857221494636544,2413138481558843201995874,633822886984823975214363968001,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord42 : orderSearch 6 6 0 [0,2417842415857221494636544,323885963880500264155966194405544,633822886984823975214363968001,2413138481558843201995874,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord43 : orderSearch 6 5 323885966298342680013187689042088 [323885966298342680013187689042088,2417842415857221494636544,633822886984823975214363968001,2413138481558843201995874,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord44 : orderSearch 6 5 323885966298342680013187689042088 [323885966298342680013187689042088,2417842415857221494636544,323885963880500264155966194405544,633822886984823975214363968001,2413138481558843201995874,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord45 : orderSearch 6 6 0 [0,2417842415857221494636544,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord46 : orderSearch 6 5 324517318136229869105186567528784 [324517318136229869105186567528784,2417842415857221494636544,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord47 : orderSearch 6 5 324517318136229869105186567528784 [324517318136229869105186567528784,2417842415857221494636544,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord48 : orderSearch 6 6 633825300114100176419220670051 [633825300114100176419220670051,633822886984823975214363968001,2413138481558843201995874,2417842415857221494636544,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord49 : orderSearch 6 6 1235522187646151016549711872 [1235522187646151016549711872,633822886984823975214363968001,323885963880500264155966194405544,2417842415857221494636544,2413138481558843201995874,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord50 : orderSearch 6 6 324518551245297441980164008661673 [324518551245297441980164008661673,633822886984823975214363968001,323885963880500264155966194405544,2417842415857221494636544,2413138481558843201995874,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord51 : orderSearch 6 6 632587360074829320473452478464 [632587360074829320473452478464,633822886984823975214363968001,324517315718387453247965072892240,2417842415857221494636544,2413138481558843201995874,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord52 : orderSearch 6 6 324518551245297447902705984381777 [324518551245297447902705984381777,633822886984823975214363968001,324517315718387453247965072892240,2417842415857221494636544,2413138481558843201995874,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord53 : orderSearch 6 6 323885966293638744586706162930922 [323885966293638744586706162930922,323885963880500264155966194405544,2417842415857221494636544,633822886984823975214363968001,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord54 : orderSearch 6 6 323885966293638744586706162930922 [323885966293638744586706162930922,2413138481558843201995874,323885963880500264155966194405544,2417842415857221494636544,633822886984823975214363968001,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord55 : orderSearch 6 6 324517318131525932550601807947122 [324517318131525932550601807947122,324517315718387453247965072892240,2417842415857221494636544,633822886984823975214363968001,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord56 : orderSearch 6 6 324517318131525932550601807947122 [324517318131525932550601807947122,2413138481558843201995874,324517315718387453247965072892240,2417842415857221494636544,633822886984823975214363968001,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord57 : orderSearch 6 6 323884728358312612082407668973568 [323884728358312612082407668973568,323885963880500264155966194405544,324517315718387453247965072892240,2417842415857221494636544,633822886984823975214363968001,2413138481558843201995874] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord58 : orderSearch 6 6 324518551240575105321523598324216 [324518551240575105321523598324216,323885963880500264155966194405544,324517315718387453247965072892240,2417842415857221494636544,633822886984823975214363968001,2413138481558843201995874] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord59 : orderSearch 7 7 2417842415857221494636544 [2417842415857221494636544,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  apply ocover_step (states := [(6,4713143110832790437888,[4713143110832790437888,2417842415857221494636544,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240]),(5,633825300114096721603068166657,[633825300114096721603068166657,2417842415857221494636544,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240]),(5,633825300114096721603068166657,[633825300114096721603068166657,2417842415857221494636544,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240]),(6,2413129272746388704198656,[2413129272746388704198656,2417842415857221494636544,2413138481558843201995874,633822886984823975214363968001,323885963880500264155966194405544,324517315718387453247965072892240]),(5,2417851624669675992433762,[2417851624669675992433762,2417842415857221494636544,633822886984823975214363968001,323885963880500264155966194405544,324517315718387453247965072892240]),(5,2417851624669675992433762,[2417851624669675992433762,2417842415857221494636544,2413138481558843201995874,633822886984823975214363968001,323885963880500264155966194405544,324517315718387453247965072892240]),(6,0,[0,2417842415857221494636544,323885963880500264155966194405544,633822886984823975214363968001,2413138481558843201995874,324517315718387453247965072892240]),(5,323885966298342680013187689042088,[323885966298342680013187689042088,2417842415857221494636544,633822886984823975214363968001,2413138481558843201995874,324517315718387453247965072892240]),(5,323885966298342680013187689042088,[323885966298342680013187689042088,2417842415857221494636544,323885963880500264155966194405544,633822886984823975214363968001,2413138481558843201995874,324517315718387453247965072892240]),(6,0,[0,2417842415857221494636544,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544]),(5,324517318136229869105186567528784,[324517318136229869105186567528784,2417842415857221494636544,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544]),(5,324517318136229869105186567528784,[324517318136229869105186567528784,2417842415857221494636544,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544]),(6,633825300114100176419220670051,[633825300114100176419220670051,633822886984823975214363968001,2413138481558843201995874,2417842415857221494636544,323885963880500264155966194405544,324517315718387453247965072892240]),(6,1235522187646151016549711872,[1235522187646151016549711872,633822886984823975214363968001,323885963880500264155966194405544,2417842415857221494636544,2413138481558843201995874,324517315718387453247965072892240]),(6,324518551245297441980164008661673,[324518551245297441980164008661673,633822886984823975214363968001,323885963880500264155966194405544,2417842415857221494636544,2413138481558843201995874,324517315718387453247965072892240]),(6,632587360074829320473452478464,[632587360074829320473452478464,633822886984823975214363968001,324517315718387453247965072892240,2417842415857221494636544,2413138481558843201995874,323885963880500264155966194405544]),(6,324518551245297447902705984381777,[324518551245297447902705984381777,633822886984823975214363968001,324517315718387453247965072892240,2417842415857221494636544,2413138481558843201995874,323885963880500264155966194405544]),(6,323885966293638744586706162930922,[323885966293638744586706162930922,323885963880500264155966194405544,2417842415857221494636544,633822886984823975214363968001,324517315718387453247965072892240]),(6,323885966293638744586706162930922,[323885966293638744586706162930922,2413138481558843201995874,323885963880500264155966194405544,2417842415857221494636544,633822886984823975214363968001,324517315718387453247965072892240]),(6,324517318131525932550601807947122,[324517318131525932550601807947122,324517315718387453247965072892240,2417842415857221494636544,633822886984823975214363968001,323885963880500264155966194405544]),(6,324517318131525932550601807947122,[324517318131525932550601807947122,2413138481558843201995874,324517315718387453247965072892240,2417842415857221494636544,633822886984823975214363968001,323885963880500264155966194405544]),(6,323884728358312612082407668973568,[323884728358312612082407668973568,323885963880500264155966194405544,324517315718387453247965072892240,2417842415857221494636544,633822886984823975214363968001,2413138481558843201995874]),(6,324518551240575105321523598324216,[324518551240575105321523598324216,323885963880500264155966194405544,324517315718387453247965072892240,2417842415857221494636544,633822886984823975214363968001,2413138481558843201995874])])
  · decide +kernel
  · simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.not_false, ord36, ord37, ord38, ord39, ord40, ord41, ord42, ord43, ord44, ord45, ord46, ord47, ord48, ord49, ord50, ord51, ord52, ord53, ord54, ord55, ord56, ord57, ord58]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord60 : orderSearch 7 7 2417842415857221494636544 [2417842415857221494636544,633825300114100176419220670051,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord61 : orderSearch 7 7 2417842415857221494636544 [2417842415857221494636544,2417842429535473200466308,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord62 : orderSearch 7 7 2417842415857221494636544 [2417842415857221494636544,633825300114100176419220670051,2417842429535473200466308,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord63 : orderSearch 7 7 633825300114113854670926499815 [633825300114113854670926499815,2417842429535473200466308,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord64 : orderSearch 7 7 633825300114113854670926499815 [633825300114113854670926499815,633825300114100176419220670051,2417842429535473200466308,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord65 : orderSearch 7 7 1235522187647279119783182368 [1235522187647279119783182368,323885963880500264155966194405544,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord66 : orderSearch 7 7 1235522187647279119783182368 [1235522187647279119783182368,633825300114100176419220670051,323885963880500264155966194405544,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord67 : orderSearch 7 7 324518553658426717053265631893227 [324518553658426717053265631893227,323885963880500264155966194405544,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord68 : orderSearch 7 7 324518553658426717053265631893227 [324518553658426717053265631893227,633825300114100176419220670051,323885963880500264155966194405544,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord69 : orderSearch 7 7 632587360074831576679919419456 [632587360074831576679919419456,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord70 : orderSearch 7 7 632587360074831576679919419456 [632587360074831576679919419456,633825300114100176419220670051,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord71 : orderSearch 7 7 324518553658426721847704374142835 [324518553658426721847704374142835,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord72 : orderSearch 7 7 324518553658426721847704374142835 [324518553658426721847704374142835,633825300114100176419220670051,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord73 : orderSearch 6 6 633825300114096721603068166657 [633825300114096721603068166657,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord74 : orderSearch 6 6 633825300114096721603068166657 [633825300114096721603068166657,633825300114110399854773996421,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord75 : orderSearch 6 6 633825300114096721603068166657 [633825300114096721603068166657,633825300114100176419220670051,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord76 : orderSearch 6 6 633825300114096721603068166657 [633825300114096721603068166657,633825300114110399854773996421,633825300114100176419220670051,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord77 : orderSearch 6 6 633825300114113854670926499815 [633825300114113854670926499815,633825300114110399854773996421,633825300114100176419220670051,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord78 : orderSearch 6 6 2413138478104027049492480 [2413138478104027049492480,633825300114110399854773996421,2417842429535473200466308,633825300114100176419220670051,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord79 : orderSearch 6 6 2413138478104027049492480 [2413138478104027049492480,633825300114110399854773996421,2413138481558843201995874,2417842429535473200466308,633825300114100176419220670051,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord80 : orderSearch 6 6 633825300114113854670926499815 [633825300114113854670926499815,633825300114110399854773996421,2413138481558843201995874,2417842429535473200466308,633825300114100176419220670051,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord81 : orderSearch 6 6 1235522187650663429483593856 [1235522187650663429483593856,633825300114110399854773996421,323885963880500264155966194405544,2417842429535473200466308,633825300114100176419220670051,2413138481558843201995874,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord82 : orderSearch 6 6 324518553658426723892391484808109 [324518553658426723892391484808109,633825300114110399854773996421,323885963880500264155966194405544,2417842429535473200466308,633825300114100176419220670051,2413138481558843201995874,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord83 : orderSearch 6 6 632587360074838345299320242432 [632587360074838345299320242432,633825300114110399854773996421,324517315718387453247965072892240,2417842429535473200466308,633825300114100176419220670051,2413138481558843201995874,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord84 : orderSearch 6 6 324518553658426725302520526646229 [324518553658426725302520526646229,633825300114110399854773996421,324517315718387453247965072892240,2417842429535473200466308,633825300114100176419220670051,2413138481558843201995874,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord85 : orderSearch 6 6 633825300114113854670926499815 [633825300114113854670926499815,2417842429535473200466308,633825300114100176419220670051,633825300114110399854773996421,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord86 : orderSearch 6 6 323885966298342689179026460989868 [323885966298342689179026460989868,323885963880500264155966194405544,633825300114110399854773996421,633825300114100176419220670051,2413138481558843201995874,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord87 : orderSearch 6 6 323885966298342689179026460989868 [323885966298342689179026460989868,2417842429535473200466308,323885963880500264155966194405544,633825300114110399854773996421,633825300114100176419220670051,2413138481558843201995874,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord88 : orderSearch 6 6 324517318136229873758612405594580 [324517318136229873758612405594580,324517315718387453247965072892240,633825300114110399854773996421,633825300114100176419220670051,2413138481558843201995874,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord89 : orderSearch 6 6 324517318136229873758612405594580 [324517318136229873758612405594580,2417842429535473200466308,324517315718387453247965072892240,633825300114110399854773996421,633825300114100176419220670051,2413138481558843201995874,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord90 : orderSearch 6 6 324518553658426717053265631893227 [324518553658426717053265631893227,633825300114100176419220670051,323885963880500264155966194405544,633825300114110399854773996421,2417842429535473200466308,2413138481558843201995874,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord91 : orderSearch 6 6 324518553658426721847704374142835 [324518553658426721847704374142835,633825300114100176419220670051,324517315718387453247965072892240,633825300114110399854773996421,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord92 : orderSearch 6 6 323885966293638744586706162930922 [323885966293638744586706162930922,323885963880500264155966194405544,633825300114110399854773996421,2417842429535473200466308,633825300114100176419220670051,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord93 : orderSearch 6 6 323885966293638744586706162930922 [323885966293638744586706162930922,2413138481558843201995874,323885963880500264155966194405544,633825300114110399854773996421,2417842429535473200466308,633825300114100176419220670051,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord94 : orderSearch 6 6 324517318131525932550601807947122 [324517318131525932550601807947122,324517315718387453247965072892240,633825300114110399854773996421,2417842429535473200466308,633825300114100176419220670051,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord95 : orderSearch 6 6 324517318131525932550601807947122 [324517318131525932550601807947122,2413138481558843201995874,324517315718387453247965072892240,633825300114110399854773996421,2417842429535473200466308,633825300114100176419220670051,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord96 : orderSearch 6 6 323884728358312612082407668973568 [323884728358312612082407668973568,323885963880500264155966194405544,324517315718387453247965072892240,633825300114110399854773996421,2417842429535473200466308,633825300114100176419220670051,2413138481558843201995874] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord97 : orderSearch 6 6 324518551240575105321523598324216 [324518551240575105321523598324216,323885963880500264155966194405544,324517315718387453247965072892240,633825300114110399854773996421,2417842429535473200466308,633825300114100176419220670051,2413138481558843201995874] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord98 : orderSearch 7 7 633825300114110399854773996421 [633825300114110399854773996421,2417842429535473200466308,633825300114100176419220670051,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  apply ocover_step (states := [(6,633825300114096721603068166657,[633825300114096721603068166657,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240]),(6,633825300114096721603068166657,[633825300114096721603068166657,633825300114110399854773996421,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240]),(6,633825300114096721603068166657,[633825300114096721603068166657,633825300114100176419220670051,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240]),(6,633825300114096721603068166657,[633825300114096721603068166657,633825300114110399854773996421,633825300114100176419220670051,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240]),(6,633825300114113854670926499815,[633825300114113854670926499815,633825300114110399854773996421,633825300114100176419220670051,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240]),(6,2413138478104027049492480,[2413138478104027049492480,633825300114110399854773996421,2417842429535473200466308,633825300114100176419220670051,323885963880500264155966194405544,324517315718387453247965072892240]),(6,2413138478104027049492480,[2413138478104027049492480,633825300114110399854773996421,2413138481558843201995874,2417842429535473200466308,633825300114100176419220670051,323885963880500264155966194405544,324517315718387453247965072892240]),(6,633825300114113854670926499815,[633825300114113854670926499815,633825300114110399854773996421,2413138481558843201995874,2417842429535473200466308,633825300114100176419220670051,323885963880500264155966194405544,324517315718387453247965072892240]),(6,1235522187650663429483593856,[1235522187650663429483593856,633825300114110399854773996421,323885963880500264155966194405544,2417842429535473200466308,633825300114100176419220670051,2413138481558843201995874,324517315718387453247965072892240]),(6,324518553658426723892391484808109,[324518553658426723892391484808109,633825300114110399854773996421,323885963880500264155966194405544,2417842429535473200466308,633825300114100176419220670051,2413138481558843201995874,324517315718387453247965072892240]),(6,632587360074838345299320242432,[632587360074838345299320242432,633825300114110399854773996421,324517315718387453247965072892240,2417842429535473200466308,633825300114100176419220670051,2413138481558843201995874,323885963880500264155966194405544]),(6,324518553658426725302520526646229,[324518553658426725302520526646229,633825300114110399854773996421,324517315718387453247965072892240,2417842429535473200466308,633825300114100176419220670051,2413138481558843201995874,323885963880500264155966194405544]),(6,633825300114113854670926499815,[633825300114113854670926499815,2417842429535473200466308,633825300114100176419220670051,633825300114110399854773996421,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240]),(6,323885966298342689179026460989868,[323885966298342689179026460989868,323885963880500264155966194405544,633825300114110399854773996421,633825300114100176419220670051,2413138481558843201995874,324517315718387453247965072892240]),(6,323885966298342689179026460989868,[323885966298342689179026460989868,2417842429535473200466308,323885963880500264155966194405544,633825300114110399854773996421,633825300114100176419220670051,2413138481558843201995874,324517315718387453247965072892240]),(6,324517318136229873758612405594580,[324517318136229873758612405594580,324517315718387453247965072892240,633825300114110399854773996421,633825300114100176419220670051,2413138481558843201995874,323885963880500264155966194405544]),(6,324517318136229873758612405594580,[324517318136229873758612405594580,2417842429535473200466308,324517315718387453247965072892240,633825300114110399854773996421,633825300114100176419220670051,2413138481558843201995874,323885963880500264155966194405544]),(6,324518553658426717053265631893227,[324518553658426717053265631893227,633825300114100176419220670051,323885963880500264155966194405544,633825300114110399854773996421,2417842429535473200466308,2413138481558843201995874,324517315718387453247965072892240]),(6,324518553658426721847704374142835,[324518553658426721847704374142835,633825300114100176419220670051,324517315718387453247965072892240,633825300114110399854773996421,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544]),(6,323885966293638744586706162930922,[323885966293638744586706162930922,323885963880500264155966194405544,633825300114110399854773996421,2417842429535473200466308,633825300114100176419220670051,324517315718387453247965072892240]),(6,323885966293638744586706162930922,[323885966293638744586706162930922,2413138481558843201995874,323885963880500264155966194405544,633825300114110399854773996421,2417842429535473200466308,633825300114100176419220670051,324517315718387453247965072892240]),(6,324517318131525932550601807947122,[324517318131525932550601807947122,324517315718387453247965072892240,633825300114110399854773996421,2417842429535473200466308,633825300114100176419220670051,323885963880500264155966194405544]),(6,324517318131525932550601807947122,[324517318131525932550601807947122,2413138481558843201995874,324517315718387453247965072892240,633825300114110399854773996421,2417842429535473200466308,633825300114100176419220670051,323885963880500264155966194405544]),(6,323884728358312612082407668973568,[323884728358312612082407668973568,323885963880500264155966194405544,324517315718387453247965072892240,633825300114110399854773996421,2417842429535473200466308,633825300114100176419220670051,2413138481558843201995874]),(6,324518551240575105321523598324216,[324518551240575105321523598324216,323885963880500264155966194405544,324517315718387453247965072892240,633825300114110399854773996421,2417842429535473200466308,633825300114100176419220670051,2413138481558843201995874])])
  · decide +kernel
  · simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.not_false, ord73, ord74, ord75, ord76, ord77, ord78, ord79, ord80, ord81, ord82, ord83, ord84, ord85, ord86, ord87, ord88, ord89, ord90, ord91, ord92, ord93, ord94, ord95, ord96, ord97]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord99 : orderSearch 7 7 633825300114110399854773996421 [633825300114110399854773996421,633822886984823975214363968001,2417842429535473200466308,633825300114100176419220670051,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord100 : orderSearch 7 7 324518551245297441980164008661673 [324518551245297441980164008661673,633822886984823975214363968001,323885963880500264155966194405544,633825300114100176419220670051,2413138481558843201995874,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord101 : orderSearch 7 7 324518551245297447902705984381777 [324518551245297447902705984381777,633822886984823975214363968001,324517315718387453247965072892240,633825300114100176419220670051,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord102 : orderSearch 7 7 323885966293638744586706162930922 [323885966293638744586706162930922,323885963880500264155966194405544,633825300114100176419220670051,633822886984823975214363968001,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord103 : orderSearch 7 7 323885966293638744586706162930922 [323885966293638744586706162930922,2413138481558843201995874,323885963880500264155966194405544,633825300114100176419220670051,633822886984823975214363968001,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord104 : orderSearch 7 7 324517318131525932550601807947122 [324517318131525932550601807947122,324517315718387453247965072892240,633825300114100176419220670051,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord105 : orderSearch 7 7 324517318131525932550601807947122 [324517318131525932550601807947122,2413138481558843201995874,324517315718387453247965072892240,633825300114100176419220670051,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord106 : orderSearch 7 7 323885966298342689179026460989868 [323885966298342689179026460989868,2417842429535473200466308,323885963880500264155966194405544,633825300114100176419220670051,633822886984823975214363968001,2413138481558843201995874,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord107 : orderSearch 7 7 324517318136229873758612405594580 [324517318136229873758612405594580,2417842429535473200466308,324517315718387453247965072892240,633825300114100176419220670051,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord108 : orderSearch 7 7 323884728358312612082407668973568 [323884728358312612082407668973568,323885963880500264155966194405544,324517315718387453247965072892240,633825300114100176419220670051,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord109 : orderSearch 7 7 324518551240575105321523598324216 [324518551240575105321523598324216,323885963880500264155966194405544,324517315718387453247965072892240,633825300114100176419220670051,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord110 : orderSearch 8 8 633825300114100176419220670051 [633825300114100176419220670051,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  apply ocover_step (states := [(7,2417842415857221494636544,[2417842415857221494636544,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240]),(7,2417842415857221494636544,[2417842415857221494636544,633825300114100176419220670051,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240]),(7,2417842415857221494636544,[2417842415857221494636544,2417842429535473200466308,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240]),(7,2417842415857221494636544,[2417842415857221494636544,633825300114100176419220670051,2417842429535473200466308,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240]),(7,633825300114113854670926499815,[633825300114113854670926499815,2417842429535473200466308,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240]),(7,633825300114113854670926499815,[633825300114113854670926499815,633825300114100176419220670051,2417842429535473200466308,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240]),(7,1235522187647279119783182368,[1235522187647279119783182368,323885963880500264155966194405544,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,324517315718387453247965072892240]),(7,1235522187647279119783182368,[1235522187647279119783182368,633825300114100176419220670051,323885963880500264155966194405544,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,324517315718387453247965072892240]),(7,324518553658426717053265631893227,[324518553658426717053265631893227,323885963880500264155966194405544,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,324517315718387453247965072892240]),(7,324518553658426717053265631893227,[324518553658426717053265631893227,633825300114100176419220670051,323885963880500264155966194405544,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,324517315718387453247965072892240]),(7,632587360074831576679919419456,[632587360074831576679919419456,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544]),(7,632587360074831576679919419456,[632587360074831576679919419456,633825300114100176419220670051,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544]),(7,324518553658426721847704374142835,[324518553658426721847704374142835,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544]),(7,324518553658426721847704374142835,[324518553658426721847704374142835,633825300114100176419220670051,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544]),(7,633825300114110399854773996421,[633825300114110399854773996421,2417842429535473200466308,633825300114100176419220670051,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240]),(7,633825300114110399854773996421,[633825300114110399854773996421,633822886984823975214363968001,2417842429535473200466308,633825300114100176419220670051,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240]),(7,324518551245297441980164008661673,[324518551245297441980164008661673,633822886984823975214363968001,323885963880500264155966194405544,633825300114100176419220670051,2413138481558843201995874,2417842429535473200466308,324517315718387453247965072892240]),(7,324518551245297447902705984381777,[324518551245297447902705984381777,633822886984823975214363968001,324517315718387453247965072892240,633825300114100176419220670051,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544]),(7,323885966293638744586706162930922,[323885966293638744586706162930922,323885963880500264155966194405544,633825300114100176419220670051,633822886984823975214363968001,2417842429535473200466308,324517315718387453247965072892240]),(7,323885966293638744586706162930922,[323885966293638744586706162930922,2413138481558843201995874,323885963880500264155966194405544,633825300114100176419220670051,633822886984823975214363968001,2417842429535473200466308,324517315718387453247965072892240]),(7,324517318131525932550601807947122,[324517318131525932550601807947122,324517315718387453247965072892240,633825300114100176419220670051,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544]),(7,324517318131525932550601807947122,[324517318131525932550601807947122,2413138481558843201995874,324517315718387453247965072892240,633825300114100176419220670051,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544]),(7,323885966298342689179026460989868,[323885966298342689179026460989868,2417842429535473200466308,323885963880500264155966194405544,633825300114100176419220670051,633822886984823975214363968001,2413138481558843201995874,324517315718387453247965072892240]),(7,324517318136229873758612405594580,[324517318136229873758612405594580,2417842429535473200466308,324517315718387453247965072892240,633825300114100176419220670051,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544]),(7,323884728358312612082407668973568,[323884728358312612082407668973568,323885963880500264155966194405544,324517315718387453247965072892240,633825300114100176419220670051,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308]),(7,324518551240575105321523598324216,[324518551240575105321523598324216,323885963880500264155966194405544,324517315718387453247965072892240,633825300114100176419220670051,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308])])
  · decide +kernel
  · simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.not_false, ord59, ord60, ord61, ord62, ord63, ord64, ord65, ord66, ord67, ord68, ord69, ord70, ord71, ord72, ord98, ord99, ord100, ord101, ord102, ord103, ord104, ord105, ord106, ord107, ord108, ord109]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord111 : orderSearch 7 7 0 [0,2413138481558843201995874,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord112 : orderSearch 7 7 0 [0,4713143110832790437888,2413138481558843201995874,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord113 : orderSearch 7 6 2417851624669675992433762 [2417851624669675992433762,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord114 : orderSearch 7 6 2417851624669675992433762 [2417851624669675992433762,4713143110832790437888,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord115 : orderSearch 7 6 2417851624669675992433762 [2417851624669675992433762,2413138481558843201995874,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord116 : orderSearch 7 6 2417851624669675992433762 [2417851624669675992433762,4713143110832790437888,2413138481558843201995874,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord117 : orderSearch 7 7 0 [0,323885963880500264155966194405544,633822886984823975214363968001,2417842429535473200466308,2413138481558843201995874,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord118 : orderSearch 7 7 0 [0,4713143110832790437888,323885963880500264155966194405544,633822886984823975214363968001,2417842429535473200466308,2413138481558843201995874,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord119 : orderSearch 7 6 323885963885213407266798984843432 [323885963885213407266798984843432,633822886984823975214363968001,2417842429535473200466308,2413138481558843201995874,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord120 : orderSearch 7 6 323885963885213407266798984843432 [323885963885213407266798984843432,4713143110832790437888,633822886984823975214363968001,2417842429535473200466308,2413138481558843201995874,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord121 : orderSearch 7 6 323885963885213407266798984843432 [323885963885213407266798984843432,323885963880500264155966194405544,633822886984823975214363968001,2417842429535473200466308,2413138481558843201995874,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord122 : orderSearch 7 6 323885963885213407266798984843432 [323885963885213407266798984843432,4713143110832790437888,323885963880500264155966194405544,633822886984823975214363968001,2417842429535473200466308,2413138481558843201995874,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord123 : orderSearch 7 7 0 [0,324517315718387453247965072892240,633822886984823975214363968001,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord124 : orderSearch 7 7 0 [0,4713143110832790437888,324517315718387453247965072892240,633822886984823975214363968001,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord125 : orderSearch 7 6 324517315723100596358797863330128 [324517315723100596358797863330128,633822886984823975214363968001,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord126 : orderSearch 7 6 324517315723100596358797863330128 [324517315723100596358797863330128,4713143110832790437888,633822886984823975214363968001,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord127 : orderSearch 7 6 324517315723100596358797863330128 [324517315723100596358797863330128,324517315718387453247965072892240,633822886984823975214363968001,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord128 : orderSearch 7 6 324517315723100596358797863330128 [324517315723100596358797863330128,4713143110832790437888,324517315718387453247965072892240,633822886984823975214363968001,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord129 : orderSearch 7 7 633825300114110399854773996421 [633825300114110399854773996421,633822886984823975214363968001,4713143110832790437888,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord130 : orderSearch 7 7 633825300114110399854773996421 [633825300114110399854773996421,633822886984823975214363968001,2417842429535473200466308,4713143110832790437888,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord131 : orderSearch 7 7 633825300114100176419220670051 [633825300114100176419220670051,633822886984823975214363968001,2413138481558843201995874,4713143110832790437888,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord132 : orderSearch 7 7 1235522187646151016549711872 [1235522187646151016549711872,633822886984823975214363968001,323885963880500264155966194405544,4713143110832790437888,2417842429535473200466308,2413138481558843201995874,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord133 : orderSearch 7 7 324518551245297441980164008661673 [324518551245297441980164008661673,633822886984823975214363968001,323885963880500264155966194405544,4713143110832790437888,2417842429535473200466308,2413138481558843201995874,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord134 : orderSearch 7 7 632587360074829320473452478464 [632587360074829320473452478464,633822886984823975214363968001,324517315718387453247965072892240,4713143110832790437888,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord135 : orderSearch 7 7 324518551245297447902705984381777 [324518551245297447902705984381777,633822886984823975214363968001,324517315718387453247965072892240,4713143110832790437888,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord136 : orderSearch 7 7 2413129272746388704198656 [2413129272746388704198656,2413138481558843201995874,4713143110832790437888,633822886984823975214363968001,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord137 : orderSearch 7 7 2413129272746388704198656 [2413129272746388704198656,2417842429535473200466308,2413138481558843201995874,4713143110832790437888,633822886984823975214363968001,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord138 : orderSearch 7 7 2417851638347927698263526 [2417851638347927698263526,2417842429535473200466308,2413138481558843201995874,4713143110832790437888,633822886984823975214363968001,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord139 : orderSearch 7 7 323885966298342689179026460989868 [323885966298342689179026460989868,2417842429535473200466308,323885963880500264155966194405544,4713143110832790437888,633822886984823975214363968001,2413138481558843201995874,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord140 : orderSearch 7 7 324517318136229873758612405594580 [324517318136229873758612405594580,2417842429535473200466308,324517315718387453247965072892240,4713143110832790437888,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord141 : orderSearch 7 7 323885966293638744586706162930922 [323885966293638744586706162930922,2413138481558843201995874,323885963880500264155966194405544,4713143110832790437888,633822886984823975214363968001,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord142 : orderSearch 7 7 324517318131525932550601807947122 [324517318131525932550601807947122,2413138481558843201995874,324517315718387453247965072892240,4713143110832790437888,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord143 : orderSearch 7 7 323884728358312612082407668973568 [323884728358312612082407668973568,323885963880500264155966194405544,324517315718387453247965072892240,4713143110832790437888,633822886984823975214363968001,2417842429535473200466308,2413138481558843201995874] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord144 : orderSearch 7 7 324518551240575105321523598324216 [324518551240575105321523598324216,323885963880500264155966194405544,324517315718387453247965072892240,4713143110832790437888,633822886984823975214363968001,2417842429535473200466308,2413138481558843201995874] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord145 : orderSearch 8 8 4713143110832790437888 [4713143110832790437888,633822886984823975214363968001,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  apply ocover_step (states := [(7,0,[0,2413138481558843201995874,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240]),(7,0,[0,4713143110832790437888,2413138481558843201995874,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240]),(6,2417851624669675992433762,[2417851624669675992433762,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240]),(6,2417851624669675992433762,[2417851624669675992433762,4713143110832790437888,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240]),(6,2417851624669675992433762,[2417851624669675992433762,2413138481558843201995874,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240]),(6,2417851624669675992433762,[2417851624669675992433762,4713143110832790437888,2413138481558843201995874,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240]),(7,0,[0,323885963880500264155966194405544,633822886984823975214363968001,2417842429535473200466308,2413138481558843201995874,324517315718387453247965072892240]),(7,0,[0,4713143110832790437888,323885963880500264155966194405544,633822886984823975214363968001,2417842429535473200466308,2413138481558843201995874,324517315718387453247965072892240]),(6,323885963885213407266798984843432,[323885963885213407266798984843432,633822886984823975214363968001,2417842429535473200466308,2413138481558843201995874,324517315718387453247965072892240]),(6,323885963885213407266798984843432,[323885963885213407266798984843432,4713143110832790437888,633822886984823975214363968001,2417842429535473200466308,2413138481558843201995874,324517315718387453247965072892240]),(6,323885963885213407266798984843432,[323885963885213407266798984843432,323885963880500264155966194405544,633822886984823975214363968001,2417842429535473200466308,2413138481558843201995874,324517315718387453247965072892240]),(6,323885963885213407266798984843432,[323885963885213407266798984843432,4713143110832790437888,323885963880500264155966194405544,633822886984823975214363968001,2417842429535473200466308,2413138481558843201995874,324517315718387453247965072892240]),(7,0,[0,324517315718387453247965072892240,633822886984823975214363968001,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544]),(7,0,[0,4713143110832790437888,324517315718387453247965072892240,633822886984823975214363968001,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544]),(6,324517315723100596358797863330128,[324517315723100596358797863330128,633822886984823975214363968001,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544]),(6,324517315723100596358797863330128,[324517315723100596358797863330128,4713143110832790437888,633822886984823975214363968001,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544]),(6,324517315723100596358797863330128,[324517315723100596358797863330128,324517315718387453247965072892240,633822886984823975214363968001,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544]),(6,324517315723100596358797863330128,[324517315723100596358797863330128,4713143110832790437888,324517315718387453247965072892240,633822886984823975214363968001,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544]),(7,633825300114110399854773996421,[633825300114110399854773996421,633822886984823975214363968001,4713143110832790437888,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240]),(7,633825300114110399854773996421,[633825300114110399854773996421,633822886984823975214363968001,2417842429535473200466308,4713143110832790437888,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240]),(7,633825300114100176419220670051,[633825300114100176419220670051,633822886984823975214363968001,2413138481558843201995874,4713143110832790437888,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240]),(7,1235522187646151016549711872,[1235522187646151016549711872,633822886984823975214363968001,323885963880500264155966194405544,4713143110832790437888,2417842429535473200466308,2413138481558843201995874,324517315718387453247965072892240]),(7,324518551245297441980164008661673,[324518551245297441980164008661673,633822886984823975214363968001,323885963880500264155966194405544,4713143110832790437888,2417842429535473200466308,2413138481558843201995874,324517315718387453247965072892240]),(7,632587360074829320473452478464,[632587360074829320473452478464,633822886984823975214363968001,324517315718387453247965072892240,4713143110832790437888,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544]),(7,324518551245297447902705984381777,[324518551245297447902705984381777,633822886984823975214363968001,324517315718387453247965072892240,4713143110832790437888,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544]),(7,2413129272746388704198656,[2413129272746388704198656,2413138481558843201995874,4713143110832790437888,633822886984823975214363968001,323885963880500264155966194405544,324517315718387453247965072892240]),(7,2413129272746388704198656,[2413129272746388704198656,2417842429535473200466308,2413138481558843201995874,4713143110832790437888,633822886984823975214363968001,323885963880500264155966194405544,324517315718387453247965072892240]),(7,2417851638347927698263526,[2417851638347927698263526,2417842429535473200466308,2413138481558843201995874,4713143110832790437888,633822886984823975214363968001,323885963880500264155966194405544,324517315718387453247965072892240]),(7,323885966298342689179026460989868,[323885966298342689179026460989868,2417842429535473200466308,323885963880500264155966194405544,4713143110832790437888,633822886984823975214363968001,2413138481558843201995874,324517315718387453247965072892240]),(7,324517318136229873758612405594580,[324517318136229873758612405594580,2417842429535473200466308,324517315718387453247965072892240,4713143110832790437888,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544]),(7,323885966293638744586706162930922,[323885966293638744586706162930922,2413138481558843201995874,323885963880500264155966194405544,4713143110832790437888,633822886984823975214363968001,2417842429535473200466308,324517315718387453247965072892240]),(7,324517318131525932550601807947122,[324517318131525932550601807947122,2413138481558843201995874,324517315718387453247965072892240,4713143110832790437888,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544]),(7,323884728358312612082407668973568,[323884728358312612082407668973568,323885963880500264155966194405544,324517315718387453247965072892240,4713143110832790437888,633822886984823975214363968001,2417842429535473200466308,2413138481558843201995874]),(7,324518551240575105321523598324216,[324518551240575105321523598324216,323885963880500264155966194405544,324517315718387453247965072892240,4713143110832790437888,633822886984823975214363968001,2417842429535473200466308,2413138481558843201995874])])
  · decide +kernel
  · simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.not_false, ord111, ord112, ord113, ord114, ord115, ord116, ord117, ord118, ord119, ord120, ord121, ord122, ord123, ord124, ord125, ord126, ord127, ord128, ord129, ord130, ord131, ord132, ord133, ord134, ord135, ord136, ord137, ord138, ord139, ord140, ord141, ord142, ord143, ord144]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord146 : orderSearch 6 6 9205357638345293824 [9205357638345293824,2413138478104027049492480,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord147 : orderSearch 6 5 633825300114096721603068166657 [633825300114096721603068166657,2413138478104027049492480,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord148 : orderSearch 6 5 633825300114096721603068166657 [633825300114096721603068166657,2413138478104027049492480,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord149 : orderSearch 6 6 2413129272746388704198656 [2413129272746388704198656,2413138478104027049492480,2417842429535473200466308,633822886984823975214363968001,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord150 : orderSearch 6 5 2417851634893111545760132 [2417851634893111545760132,2413138478104027049492480,633822886984823975214363968001,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord151 : orderSearch 6 5 2417851634893111545760132 [2417851634893111545760132,2413138478104027049492480,2417842429535473200466308,633822886984823975214363968001,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord152 : orderSearch 6 6 0 [0,2413138478104027049492480,323885963880500264155966194405544,633822886984823975214363968001,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord153 : orderSearch 6 5 323885966293638742259993243898024 [323885966293638742259993243898024,2413138478104027049492480,633822886984823975214363968001,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord154 : orderSearch 6 5 323885966293638742259993243898024 [323885966293638742259993243898024,2413138478104027049492480,323885963880500264155966194405544,633822886984823975214363968001,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord155 : orderSearch 6 6 0 [0,2413138478104027049492480,324517315718387453247965072892240,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord156 : orderSearch 6 5 324517318131525931351992122384720 [324517318131525931351992122384720,2413138478104027049492480,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord157 : orderSearch 6 5 324517318131525931351992122384720 [324517318131525931351992122384720,2413138478104027049492480,324517315718387453247965072892240,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord158 : orderSearch 6 6 633825300114110399854773996421 [633825300114110399854773996421,633822886984823975214363968001,2417842429535473200466308,2413138478104027049492480,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord159 : orderSearch 6 6 1235522187646151016549711872 [1235522187646151016549711872,633822886984823975214363968001,323885963880500264155966194405544,2413138478104027049492480,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord160 : orderSearch 6 6 324518551245297441980164008661673 [324518551245297441980164008661673,633822886984823975214363968001,323885963880500264155966194405544,2413138478104027049492480,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord161 : orderSearch 6 6 632587360074829320473452478464 [632587360074829320473452478464,633822886984823975214363968001,324517315718387453247965072892240,2413138478104027049492480,2417842429535473200466308,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord162 : orderSearch 6 6 324518551245297447902705984381777 [324518551245297447902705984381777,633822886984823975214363968001,324517315718387453247965072892240,2413138478104027049492480,2417842429535473200466308,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord163 : orderSearch 6 6 323885966298342689179026460989868 [323885966298342689179026460989868,323885963880500264155966194405544,2413138478104027049492480,633822886984823975214363968001,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord164 : orderSearch 6 6 323885966298342689179026460989868 [323885966298342689179026460989868,2417842429535473200466308,323885963880500264155966194405544,2413138478104027049492480,633822886984823975214363968001,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord165 : orderSearch 6 6 324517318136229873758612405594580 [324517318136229873758612405594580,324517315718387453247965072892240,2413138478104027049492480,633822886984823975214363968001,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord166 : orderSearch 6 6 324517318136229873758612405594580 [324517318136229873758612405594580,2417842429535473200466308,324517315718387453247965072892240,2413138478104027049492480,633822886984823975214363968001,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord167 : orderSearch 6 6 323884728358312612082407668973568 [323884728358312612082407668973568,323885963880500264155966194405544,324517315718387453247965072892240,2413138478104027049492480,633822886984823975214363968001,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord168 : orderSearch 6 6 324518551240575105321523598324216 [324518551240575105321523598324216,323885963880500264155966194405544,324517315718387453247965072892240,2413138478104027049492480,633822886984823975214363968001,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord169 : orderSearch 7 7 2413138478104027049492480 [2413138478104027049492480,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  apply ocover_step (states := [(6,9205357638345293824,[9205357638345293824,2413138478104027049492480,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240]),(5,633825300114096721603068166657,[633825300114096721603068166657,2413138478104027049492480,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240]),(5,633825300114096721603068166657,[633825300114096721603068166657,2413138478104027049492480,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240]),(6,2413129272746388704198656,[2413129272746388704198656,2413138478104027049492480,2417842429535473200466308,633822886984823975214363968001,323885963880500264155966194405544,324517315718387453247965072892240]),(5,2417851634893111545760132,[2417851634893111545760132,2413138478104027049492480,633822886984823975214363968001,323885963880500264155966194405544,324517315718387453247965072892240]),(5,2417851634893111545760132,[2417851634893111545760132,2413138478104027049492480,2417842429535473200466308,633822886984823975214363968001,323885963880500264155966194405544,324517315718387453247965072892240]),(6,0,[0,2413138478104027049492480,323885963880500264155966194405544,633822886984823975214363968001,2417842429535473200466308,324517315718387453247965072892240]),(5,323885966293638742259993243898024,[323885966293638742259993243898024,2413138478104027049492480,633822886984823975214363968001,2417842429535473200466308,324517315718387453247965072892240]),(5,323885966293638742259993243898024,[323885966293638742259993243898024,2413138478104027049492480,323885963880500264155966194405544,633822886984823975214363968001,2417842429535473200466308,324517315718387453247965072892240]),(6,0,[0,2413138478104027049492480,324517315718387453247965072892240,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544]),(5,324517318131525931351992122384720,[324517318131525931351992122384720,2413138478104027049492480,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544]),(5,324517318131525931351992122384720,[324517318131525931351992122384720,2413138478104027049492480,324517315718387453247965072892240,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544]),(6,633825300114110399854773996421,[633825300114110399854773996421,633822886984823975214363968001,2417842429535473200466308,2413138478104027049492480,323885963880500264155966194405544,324517315718387453247965072892240]),(6,1235522187646151016549711872,[1235522187646151016549711872,633822886984823975214363968001,323885963880500264155966194405544,2413138478104027049492480,2417842429535473200466308,324517315718387453247965072892240]),(6,324518551245297441980164008661673,[324518551245297441980164008661673,633822886984823975214363968001,323885963880500264155966194405544,2413138478104027049492480,2417842429535473200466308,324517315718387453247965072892240]),(6,632587360074829320473452478464,[632587360074829320473452478464,633822886984823975214363968001,324517315718387453247965072892240,2413138478104027049492480,2417842429535473200466308,323885963880500264155966194405544]),(6,324518551245297447902705984381777,[324518551245297447902705984381777,633822886984823975214363968001,324517315718387453247965072892240,2413138478104027049492480,2417842429535473200466308,323885963880500264155966194405544]),(6,323885966298342689179026460989868,[323885966298342689179026460989868,323885963880500264155966194405544,2413138478104027049492480,633822886984823975214363968001,324517315718387453247965072892240]),(6,323885966298342689179026460989868,[323885966298342689179026460989868,2417842429535473200466308,323885963880500264155966194405544,2413138478104027049492480,633822886984823975214363968001,324517315718387453247965072892240]),(6,324517318136229873758612405594580,[324517318136229873758612405594580,324517315718387453247965072892240,2413138478104027049492480,633822886984823975214363968001,323885963880500264155966194405544]),(6,324517318136229873758612405594580,[324517318136229873758612405594580,2417842429535473200466308,324517315718387453247965072892240,2413138478104027049492480,633822886984823975214363968001,323885963880500264155966194405544]),(6,323884728358312612082407668973568,[323884728358312612082407668973568,323885963880500264155966194405544,324517315718387453247965072892240,2413138478104027049492480,633822886984823975214363968001,2417842429535473200466308]),(6,324518551240575105321523598324216,[324518551240575105321523598324216,323885963880500264155966194405544,324517315718387453247965072892240,2413138478104027049492480,633822886984823975214363968001,2417842429535473200466308])])
  · decide +kernel
  · simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.not_false, ord146, ord147, ord148, ord149, ord150, ord151, ord152, ord153, ord154, ord155, ord156, ord157, ord158, ord159, ord160, ord161, ord162, ord163, ord164, ord165, ord166, ord167, ord168]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord170 : orderSearch 7 7 2413138478104027049492480 [2413138478104027049492480,633825300114110399854773996421,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord171 : orderSearch 7 7 2413138478104027049492480 [2413138478104027049492480,2413138481558843201995874,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord172 : orderSearch 7 7 2413138478104027049492480 [2413138478104027049492480,633825300114110399854773996421,2413138481558843201995874,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord173 : orderSearch 7 7 633825300114113854670926499815 [633825300114113854670926499815,2413138481558843201995874,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord174 : orderSearch 7 7 633825300114113854670926499815 [633825300114113854670926499815,633825300114110399854773996421,2413138481558843201995874,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord175 : orderSearch 7 7 1235522187650663429483593856 [1235522187650663429483593856,323885963880500264155966194405544,633822886984823975214363968001,2417842429535473200466308,2413138481558843201995874,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord176 : orderSearch 7 7 1235522187650663429483593856 [1235522187650663429483593856,633825300114110399854773996421,323885963880500264155966194405544,633822886984823975214363968001,2417842429535473200466308,2413138481558843201995874,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord177 : orderSearch 7 7 324518553658426723892391484808109 [324518553658426723892391484808109,323885963880500264155966194405544,633822886984823975214363968001,2417842429535473200466308,2413138481558843201995874,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord178 : orderSearch 7 7 324518553658426723892391484808109 [324518553658426723892391484808109,633825300114110399854773996421,323885963880500264155966194405544,633822886984823975214363968001,2417842429535473200466308,2413138481558843201995874,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord179 : orderSearch 7 7 632587360074838345299320242432 [632587360074838345299320242432,324517315718387453247965072892240,633822886984823975214363968001,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord180 : orderSearch 7 7 632587360074838345299320242432 [632587360074838345299320242432,633825300114110399854773996421,324517315718387453247965072892240,633822886984823975214363968001,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord181 : orderSearch 7 7 324518553658426725302520526646229 [324518553658426725302520526646229,324517315718387453247965072892240,633822886984823975214363968001,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord182 : orderSearch 7 7 324518553658426725302520526646229 [324518553658426725302520526646229,633825300114110399854773996421,324517315718387453247965072892240,633822886984823975214363968001,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord183 : orderSearch 7 7 324518551245297441980164008661673 [324518551245297441980164008661673,633822886984823975214363968001,323885963880500264155966194405544,633825300114110399854773996421,2417842429535473200466308,2413138481558843201995874,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord184 : orderSearch 7 7 324518551245297447902705984381777 [324518551245297447902705984381777,633822886984823975214363968001,324517315718387453247965072892240,633825300114110399854773996421,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord185 : orderSearch 7 7 323885966298342689179026460989868 [323885966298342689179026460989868,323885963880500264155966194405544,633825300114110399854773996421,633822886984823975214363968001,2413138481558843201995874,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord186 : orderSearch 7 7 323885966298342689179026460989868 [323885966298342689179026460989868,2417842429535473200466308,323885963880500264155966194405544,633825300114110399854773996421,633822886984823975214363968001,2413138481558843201995874,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord187 : orderSearch 7 7 324517318136229873758612405594580 [324517318136229873758612405594580,324517315718387453247965072892240,633825300114110399854773996421,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord188 : orderSearch 7 7 324517318136229873758612405594580 [324517318136229873758612405594580,2417842429535473200466308,324517315718387453247965072892240,633825300114110399854773996421,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord189 : orderSearch 7 7 323885966293638744586706162930922 [323885966293638744586706162930922,2413138481558843201995874,323885963880500264155966194405544,633825300114110399854773996421,633822886984823975214363968001,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord190 : orderSearch 7 7 324517318131525932550601807947122 [324517318131525932550601807947122,2413138481558843201995874,324517315718387453247965072892240,633825300114110399854773996421,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord191 : orderSearch 7 7 323884728358312612082407668973568 [323884728358312612082407668973568,323885963880500264155966194405544,324517315718387453247965072892240,633825300114110399854773996421,633822886984823975214363968001,2417842429535473200466308,2413138481558843201995874] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord192 : orderSearch 7 7 324518551240575105321523598324216 [324518551240575105321523598324216,323885963880500264155966194405544,324517315718387453247965072892240,633825300114110399854773996421,633822886984823975214363968001,2417842429535473200466308,2413138481558843201995874] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord193 : orderSearch 8 8 633825300114110399854773996421 [633825300114110399854773996421,633822886984823975214363968001,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  apply ocover_step (states := [(7,2413138478104027049492480,[2413138478104027049492480,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240]),(7,2413138478104027049492480,[2413138478104027049492480,633825300114110399854773996421,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240]),(7,2413138478104027049492480,[2413138478104027049492480,2413138481558843201995874,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240]),(7,2413138478104027049492480,[2413138478104027049492480,633825300114110399854773996421,2413138481558843201995874,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240]),(7,633825300114113854670926499815,[633825300114113854670926499815,2413138481558843201995874,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240]),(7,633825300114113854670926499815,[633825300114113854670926499815,633825300114110399854773996421,2413138481558843201995874,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240]),(7,1235522187650663429483593856,[1235522187650663429483593856,323885963880500264155966194405544,633822886984823975214363968001,2417842429535473200466308,2413138481558843201995874,324517315718387453247965072892240]),(7,1235522187650663429483593856,[1235522187650663429483593856,633825300114110399854773996421,323885963880500264155966194405544,633822886984823975214363968001,2417842429535473200466308,2413138481558843201995874,324517315718387453247965072892240]),(7,324518553658426723892391484808109,[324518553658426723892391484808109,323885963880500264155966194405544,633822886984823975214363968001,2417842429535473200466308,2413138481558843201995874,324517315718387453247965072892240]),(7,324518553658426723892391484808109,[324518553658426723892391484808109,633825300114110399854773996421,323885963880500264155966194405544,633822886984823975214363968001,2417842429535473200466308,2413138481558843201995874,324517315718387453247965072892240]),(7,632587360074838345299320242432,[632587360074838345299320242432,324517315718387453247965072892240,633822886984823975214363968001,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544]),(7,632587360074838345299320242432,[632587360074838345299320242432,633825300114110399854773996421,324517315718387453247965072892240,633822886984823975214363968001,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544]),(7,324518553658426725302520526646229,[324518553658426725302520526646229,324517315718387453247965072892240,633822886984823975214363968001,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544]),(7,324518553658426725302520526646229,[324518553658426725302520526646229,633825300114110399854773996421,324517315718387453247965072892240,633822886984823975214363968001,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544]),(7,324518551245297441980164008661673,[324518551245297441980164008661673,633822886984823975214363968001,323885963880500264155966194405544,633825300114110399854773996421,2417842429535473200466308,2413138481558843201995874,324517315718387453247965072892240]),(7,324518551245297447902705984381777,[324518551245297447902705984381777,633822886984823975214363968001,324517315718387453247965072892240,633825300114110399854773996421,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544]),(7,323885966298342689179026460989868,[323885966298342689179026460989868,323885963880500264155966194405544,633825300114110399854773996421,633822886984823975214363968001,2413138481558843201995874,324517315718387453247965072892240]),(7,323885966298342689179026460989868,[323885966298342689179026460989868,2417842429535473200466308,323885963880500264155966194405544,633825300114110399854773996421,633822886984823975214363968001,2413138481558843201995874,324517315718387453247965072892240]),(7,324517318136229873758612405594580,[324517318136229873758612405594580,324517315718387453247965072892240,633825300114110399854773996421,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544]),(7,324517318136229873758612405594580,[324517318136229873758612405594580,2417842429535473200466308,324517315718387453247965072892240,633825300114110399854773996421,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544]),(7,323885966293638744586706162930922,[323885966293638744586706162930922,2413138481558843201995874,323885963880500264155966194405544,633825300114110399854773996421,633822886984823975214363968001,2417842429535473200466308,324517315718387453247965072892240]),(7,324517318131525932550601807947122,[324517318131525932550601807947122,2413138481558843201995874,324517315718387453247965072892240,633825300114110399854773996421,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544]),(7,323884728358312612082407668973568,[323884728358312612082407668973568,323885963880500264155966194405544,324517315718387453247965072892240,633825300114110399854773996421,633822886984823975214363968001,2417842429535473200466308,2413138481558843201995874]),(7,324518551240575105321523598324216,[324518551240575105321523598324216,323885963880500264155966194405544,324517315718387453247965072892240,633825300114110399854773996421,633822886984823975214363968001,2417842429535473200466308,2413138481558843201995874])])
  · decide +kernel
  · simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.not_false, ord169, ord170, ord171, ord172, ord173, ord174, ord175, ord176, ord177, ord178, ord179, ord180, ord181, ord182, ord183, ord184, ord185, ord186, ord187, ord188, ord189, ord190, ord191, ord192]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord194 : orderSearch 7 7 0 [0,2413138481558843201995874,633822886984823975214363968001,323885963880500264155966194405544,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord195 : orderSearch 7 7 0 [0,1235522187646151016549711872,2413138481558843201995874,633822886984823975214363968001,323885963880500264155966194405544,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord196 : orderSearch 7 6 1237935326127709859751707746 [1237935326127709859751707746,633822886984823975214363968001,323885963880500264155966194405544,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord197 : orderSearch 7 6 1237935326127709859751707746 [1237935326127709859751707746,1235522187646151016549711872,633822886984823975214363968001,323885963880500264155966194405544,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord198 : orderSearch 7 6 1237935326127709859751707746 [1237935326127709859751707746,2413138481558843201995874,633822886984823975214363968001,323885963880500264155966194405544,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord199 : orderSearch 7 6 1237935326127709859751707746 [1237935326127709859751707746,1235522187646151016549711872,2413138481558843201995874,633822886984823975214363968001,323885963880500264155966194405544,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord200 : orderSearch 7 7 0 [0,2417842429535473200466308,633822886984823975214363968001,323885963880500264155966194405544,2413138481558843201995874,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord201 : orderSearch 7 7 0 [0,1235522187646151016549711872,2417842429535473200466308,633822886984823975214363968001,323885963880500264155966194405544,2413138481558843201995874,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord202 : orderSearch 7 6 1237940030075686489750178180 [1237940030075686489750178180,633822886984823975214363968001,323885963880500264155966194405544,2413138481558843201995874,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord203 : orderSearch 7 6 1237940030075686489750178180 [1237940030075686489750178180,1235522187646151016549711872,633822886984823975214363968001,323885963880500264155966194405544,2413138481558843201995874,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord204 : orderSearch 7 6 1237940030075686489750178180 [1237940030075686489750178180,2417842429535473200466308,633822886984823975214363968001,323885963880500264155966194405544,2413138481558843201995874,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord205 : orderSearch 7 6 1237940030075686489750178180 [1237940030075686489750178180,1235522187646151016549711872,2417842429535473200466308,633822886984823975214363968001,323885963880500264155966194405544,2413138481558843201995874,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord206 : orderSearch 7 7 0 [0,324517315718387453247965072892240,633822886984823975214363968001,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord207 : orderSearch 7 7 0 [0,1235522187646151016549711872,324517315718387453247965072892240,633822886984823975214363968001,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord208 : orderSearch 7 6 324518551240575099398981622604112 [324518551240575099398981622604112,633822886984823975214363968001,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord209 : orderSearch 7 6 324518551240575099398981622604112 [324518551240575099398981622604112,1235522187646151016549711872,633822886984823975214363968001,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord210 : orderSearch 7 6 324518551240575099398981622604112 [324518551240575099398981622604112,324517315718387453247965072892240,633822886984823975214363968001,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord211 : orderSearch 7 6 324518551240575099398981622604112 [324518551240575099398981622604112,1235522187646151016549711872,324517315718387453247965072892240,633822886984823975214363968001,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord212 : orderSearch 7 7 324518551245297441980164008661673 [324518551245297441980164008661673,633822886984823975214363968001,1235522187646151016549711872,2413138481558843201995874,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord213 : orderSearch 7 7 324518551245297441980164008661673 [324518551245297441980164008661673,633822886984823975214363968001,323885963880500264155966194405544,1235522187646151016549711872,2413138481558843201995874,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord214 : orderSearch 7 7 633825300114100176419220670051 [633825300114100176419220670051,633822886984823975214363968001,2413138481558843201995874,1235522187646151016549711872,323885963880500264155966194405544,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord215 : orderSearch 7 7 633825300114110399854773996421 [633825300114110399854773996421,633822886984823975214363968001,2417842429535473200466308,1235522187646151016549711872,323885963880500264155966194405544,2413138481558843201995874,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord216 : orderSearch 7 7 632587360074829320473452478464 [632587360074829320473452478464,633822886984823975214363968001,324517315718387453247965072892240,1235522187646151016549711872,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord217 : orderSearch 7 7 324518551245297447902705984381777 [324518551245297447902705984381777,633822886984823975214363968001,324517315718387453247965072892240,1235522187646151016549711872,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord218 : orderSearch 7 7 323885966293638744586706162930922 [323885966293638744586706162930922,323885963880500264155966194405544,2413138481558843201995874,1235522187646151016549711872,633822886984823975214363968001,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord219 : orderSearch 7 7 323885966298342689179026460989868 [323885966298342689179026460989868,323885963880500264155966194405544,2417842429535473200466308,1235522187646151016549711872,633822886984823975214363968001,2413138481558843201995874,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord220 : orderSearch 7 7 323884728358312612082407668973568 [323884728358312612082407668973568,324517315718387453247965072892240,1235522187646151016549711872,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord221 : orderSearch 7 7 323884728358312612082407668973568 [323884728358312612082407668973568,323885963880500264155966194405544,324517315718387453247965072892240,1235522187646151016549711872,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord222 : orderSearch 7 7 324518551240575105321523598324216 [324518551240575105321523598324216,323885963880500264155966194405544,324517315718387453247965072892240,1235522187646151016549711872,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord223 : orderSearch 7 7 324517318131525932550601807947122 [324517318131525932550601807947122,2413138481558843201995874,324517315718387453247965072892240,1235522187646151016549711872,633822886984823975214363968001,323885963880500264155966194405544,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord224 : orderSearch 7 7 324517318136229873758612405594580 [324517318136229873758612405594580,2417842429535473200466308,324517315718387453247965072892240,1235522187646151016549711872,633822886984823975214363968001,323885963880500264155966194405544,2413138481558843201995874] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord225 : orderSearch 8 8 1235522187646151016549711872 [1235522187646151016549711872,633822886984823975214363968001,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308,324517315718387453247965072892240] = false := by
  apply ocover_step (states := [(7,0,[0,2413138481558843201995874,633822886984823975214363968001,323885963880500264155966194405544,2417842429535473200466308,324517315718387453247965072892240]),(7,0,[0,1235522187646151016549711872,2413138481558843201995874,633822886984823975214363968001,323885963880500264155966194405544,2417842429535473200466308,324517315718387453247965072892240]),(6,1237935326127709859751707746,[1237935326127709859751707746,633822886984823975214363968001,323885963880500264155966194405544,2417842429535473200466308,324517315718387453247965072892240]),(6,1237935326127709859751707746,[1237935326127709859751707746,1235522187646151016549711872,633822886984823975214363968001,323885963880500264155966194405544,2417842429535473200466308,324517315718387453247965072892240]),(6,1237935326127709859751707746,[1237935326127709859751707746,2413138481558843201995874,633822886984823975214363968001,323885963880500264155966194405544,2417842429535473200466308,324517315718387453247965072892240]),(6,1237935326127709859751707746,[1237935326127709859751707746,1235522187646151016549711872,2413138481558843201995874,633822886984823975214363968001,323885963880500264155966194405544,2417842429535473200466308,324517315718387453247965072892240]),(7,0,[0,2417842429535473200466308,633822886984823975214363968001,323885963880500264155966194405544,2413138481558843201995874,324517315718387453247965072892240]),(7,0,[0,1235522187646151016549711872,2417842429535473200466308,633822886984823975214363968001,323885963880500264155966194405544,2413138481558843201995874,324517315718387453247965072892240]),(6,1237940030075686489750178180,[1237940030075686489750178180,633822886984823975214363968001,323885963880500264155966194405544,2413138481558843201995874,324517315718387453247965072892240]),(6,1237940030075686489750178180,[1237940030075686489750178180,1235522187646151016549711872,633822886984823975214363968001,323885963880500264155966194405544,2413138481558843201995874,324517315718387453247965072892240]),(6,1237940030075686489750178180,[1237940030075686489750178180,2417842429535473200466308,633822886984823975214363968001,323885963880500264155966194405544,2413138481558843201995874,324517315718387453247965072892240]),(6,1237940030075686489750178180,[1237940030075686489750178180,1235522187646151016549711872,2417842429535473200466308,633822886984823975214363968001,323885963880500264155966194405544,2413138481558843201995874,324517315718387453247965072892240]),(7,0,[0,324517315718387453247965072892240,633822886984823975214363968001,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308]),(7,0,[0,1235522187646151016549711872,324517315718387453247965072892240,633822886984823975214363968001,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308]),(6,324518551240575099398981622604112,[324518551240575099398981622604112,633822886984823975214363968001,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308]),(6,324518551240575099398981622604112,[324518551240575099398981622604112,1235522187646151016549711872,633822886984823975214363968001,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308]),(6,324518551240575099398981622604112,[324518551240575099398981622604112,324517315718387453247965072892240,633822886984823975214363968001,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308]),(6,324518551240575099398981622604112,[324518551240575099398981622604112,1235522187646151016549711872,324517315718387453247965072892240,633822886984823975214363968001,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308]),(7,324518551245297441980164008661673,[324518551245297441980164008661673,633822886984823975214363968001,1235522187646151016549711872,2413138481558843201995874,2417842429535473200466308,324517315718387453247965072892240]),(7,324518551245297441980164008661673,[324518551245297441980164008661673,633822886984823975214363968001,323885963880500264155966194405544,1235522187646151016549711872,2413138481558843201995874,2417842429535473200466308,324517315718387453247965072892240]),(7,633825300114100176419220670051,[633825300114100176419220670051,633822886984823975214363968001,2413138481558843201995874,1235522187646151016549711872,323885963880500264155966194405544,2417842429535473200466308,324517315718387453247965072892240]),(7,633825300114110399854773996421,[633825300114110399854773996421,633822886984823975214363968001,2417842429535473200466308,1235522187646151016549711872,323885963880500264155966194405544,2413138481558843201995874,324517315718387453247965072892240]),(7,632587360074829320473452478464,[632587360074829320473452478464,633822886984823975214363968001,324517315718387453247965072892240,1235522187646151016549711872,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308]),(7,324518551245297447902705984381777,[324518551245297447902705984381777,633822886984823975214363968001,324517315718387453247965072892240,1235522187646151016549711872,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308]),(7,323885966293638744586706162930922,[323885966293638744586706162930922,323885963880500264155966194405544,2413138481558843201995874,1235522187646151016549711872,633822886984823975214363968001,2417842429535473200466308,324517315718387453247965072892240]),(7,323885966298342689179026460989868,[323885966298342689179026460989868,323885963880500264155966194405544,2417842429535473200466308,1235522187646151016549711872,633822886984823975214363968001,2413138481558843201995874,324517315718387453247965072892240]),(7,323884728358312612082407668973568,[323884728358312612082407668973568,324517315718387453247965072892240,1235522187646151016549711872,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308]),(7,323884728358312612082407668973568,[323884728358312612082407668973568,323885963880500264155966194405544,324517315718387453247965072892240,1235522187646151016549711872,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308]),(7,324518551240575105321523598324216,[324518551240575105321523598324216,323885963880500264155966194405544,324517315718387453247965072892240,1235522187646151016549711872,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308]),(7,324517318131525932550601807947122,[324517318131525932550601807947122,2413138481558843201995874,324517315718387453247965072892240,1235522187646151016549711872,633822886984823975214363968001,323885963880500264155966194405544,2417842429535473200466308]),(7,324517318136229873758612405594580,[324517318136229873758612405594580,2417842429535473200466308,324517315718387453247965072892240,1235522187646151016549711872,633822886984823975214363968001,323885963880500264155966194405544,2413138481558843201995874])])
  · decide +kernel
  · simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.not_false, ord194, ord195, ord196, ord197, ord198, ord199, ord200, ord201, ord202, ord203, ord204, ord205, ord206, ord207, ord208, ord209, ord210, ord211, ord212, ord213, ord214, ord215, ord216, ord217, ord218, ord219, ord220, ord221, ord222, ord223, ord224]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord226 : orderSearch 7 7 9206485741578764320 [9206485741578764320,2413138481558843201995874,633822886984823975214363968001,323885963880500264155966194405544,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord227 : orderSearch 7 7 9206485741578764320 [9206485741578764320,324518551245297441980164008661673,2413138481558843201995874,633822886984823975214363968001,323885963880500264155966194405544,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord228 : orderSearch 7 7 324518553658426717053265631893227 [324518553658426717053265631893227,2413138481558843201995874,633822886984823975214363968001,323885963880500264155966194405544,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord229 : orderSearch 7 7 324518553658426717053265631893227 [324518553658426717053265631893227,324518551245297441980164008661673,2413138481558843201995874,633822886984823975214363968001,323885963880500264155966194405544,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord230 : orderSearch 7 7 4713147623245724319872 [4713147623245724319872,2417842429535473200466308,633822886984823975214363968001,323885963880500264155966194405544,2413138481558843201995874,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord231 : orderSearch 7 7 4713147623245724319872 [4713147623245724319872,324518551245297441980164008661673,2417842429535473200466308,633822886984823975214363968001,323885963880500264155966194405544,2413138481558843201995874,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord232 : orderSearch 7 7 324518553658426723892391484808109 [324518553658426723892391484808109,2417842429535473200466308,633822886984823975214363968001,323885963880500264155966194405544,2413138481558843201995874,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord233 : orderSearch 7 7 324518553658426723892391484808109 [324518553658426723892391484808109,324518551245297441980164008661673,2417842429535473200466308,633822886984823975214363968001,323885963880500264155966194405544,2413138481558843201995874,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord234 : orderSearch 7 7 324517315718387441402881121452032 [324517315718387441402881121452032,633822886984823975214363968001,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord235 : orderSearch 7 7 324517315718387441402881121452032 [324517315718387441402881121452032,324518551245297441980164008661673,633822886984823975214363968001,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord236 : orderSearch 7 7 324517315718387441402881121452032 [324517315718387441402881121452032,324517315718387453247965072892240,633822886984823975214363968001,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord237 : orderSearch 7 7 324517315718387441402881121452032 [324517315718387441402881121452032,324518551245297441980164008661673,324517315718387453247965072892240,633822886984823975214363968001,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord238 : orderSearch 7 7 324518551245297453825247960101881 [324518551245297453825247960101881,324517315718387453247965072892240,633822886984823975214363968001,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord239 : orderSearch 7 7 324518551245297453825247960101881 [324518551245297453825247960101881,324518551245297441980164008661673,324517315718387453247965072892240,633822886984823975214363968001,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord240 : orderSearch 7 7 324518551245297447902705984381777 [324518551245297447902705984381777,324517315718387453247965072892240,324518551245297441980164008661673,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord241 : orderSearch 7 7 324518551245297447902705984381777 [324518551245297447902705984381777,633822886984823975214363968001,324517315718387453247965072892240,324518551245297441980164008661673,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord242 : orderSearch 8 8 324518551245297441980164008661673 [324518551245297441980164008661673,633822886984823975214363968001,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308,324517315718387453247965072892240] = false := by
  apply ocover_step (states := [(7,9206485741578764320,[9206485741578764320,2413138481558843201995874,633822886984823975214363968001,323885963880500264155966194405544,2417842429535473200466308,324517315718387453247965072892240]),(7,9206485741578764320,[9206485741578764320,324518551245297441980164008661673,2413138481558843201995874,633822886984823975214363968001,323885963880500264155966194405544,2417842429535473200466308,324517315718387453247965072892240]),(7,324518553658426717053265631893227,[324518553658426717053265631893227,2413138481558843201995874,633822886984823975214363968001,323885963880500264155966194405544,2417842429535473200466308,324517315718387453247965072892240]),(7,324518553658426717053265631893227,[324518553658426717053265631893227,324518551245297441980164008661673,2413138481558843201995874,633822886984823975214363968001,323885963880500264155966194405544,2417842429535473200466308,324517315718387453247965072892240]),(7,4713147623245724319872,[4713147623245724319872,2417842429535473200466308,633822886984823975214363968001,323885963880500264155966194405544,2413138481558843201995874,324517315718387453247965072892240]),(7,4713147623245724319872,[4713147623245724319872,324518551245297441980164008661673,2417842429535473200466308,633822886984823975214363968001,323885963880500264155966194405544,2413138481558843201995874,324517315718387453247965072892240]),(7,324518553658426723892391484808109,[324518553658426723892391484808109,2417842429535473200466308,633822886984823975214363968001,323885963880500264155966194405544,2413138481558843201995874,324517315718387453247965072892240]),(7,324518553658426723892391484808109,[324518553658426723892391484808109,324518551245297441980164008661673,2417842429535473200466308,633822886984823975214363968001,323885963880500264155966194405544,2413138481558843201995874,324517315718387453247965072892240]),(7,324517315718387441402881121452032,[324517315718387441402881121452032,633822886984823975214363968001,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308]),(7,324517315718387441402881121452032,[324517315718387441402881121452032,324518551245297441980164008661673,633822886984823975214363968001,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308]),(7,324517315718387441402881121452032,[324517315718387441402881121452032,324517315718387453247965072892240,633822886984823975214363968001,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308]),(7,324517315718387441402881121452032,[324517315718387441402881121452032,324518551245297441980164008661673,324517315718387453247965072892240,633822886984823975214363968001,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308]),(7,324518551245297453825247960101881,[324518551245297453825247960101881,324517315718387453247965072892240,633822886984823975214363968001,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308]),(7,324518551245297453825247960101881,[324518551245297453825247960101881,324518551245297441980164008661673,324517315718387453247965072892240,633822886984823975214363968001,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308]),(7,324518551245297447902705984381777,[324518551245297447902705984381777,324517315718387453247965072892240,324518551245297441980164008661673,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308]),(7,324518551245297447902705984381777,[324518551245297447902705984381777,633822886984823975214363968001,324517315718387453247965072892240,324518551245297441980164008661673,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308])])
  · decide +kernel
  · simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.not_false, ord226, ord227, ord228, ord229, ord230, ord231, ord232, ord233, ord234, ord235, ord236, ord237, ord238, ord239, ord240, ord241]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord243 : orderSearch 7 7 0 [0,2413138481558843201995874,633822886984823975214363968001,324517315718387453247965072892240,2417842429535473200466308,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord244 : orderSearch 7 7 0 [0,632587360074829320473452478464,2413138481558843201995874,633822886984823975214363968001,324517315718387453247965072892240,2417842429535473200466308,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord245 : orderSearch 7 6 632589773213310879316654474338 [632589773213310879316654474338,633822886984823975214363968001,324517315718387453247965072892240,2417842429535473200466308,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord246 : orderSearch 7 6 632589773213310879316654474338 [632589773213310879316654474338,632587360074829320473452478464,633822886984823975214363968001,324517315718387453247965072892240,2417842429535473200466308,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord247 : orderSearch 7 6 632589773213310879316654474338 [632589773213310879316654474338,2413138481558843201995874,633822886984823975214363968001,324517315718387453247965072892240,2417842429535473200466308,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord248 : orderSearch 7 6 632589773213310879316654474338 [632589773213310879316654474338,632587360074829320473452478464,2413138481558843201995874,633822886984823975214363968001,324517315718387453247965072892240,2417842429535473200466308,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord249 : orderSearch 7 7 0 [0,2417842429535473200466308,633822886984823975214363968001,324517315718387453247965072892240,2413138481558843201995874,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord250 : orderSearch 7 7 0 [0,632587360074829320473452478464,2417842429535473200466308,633822886984823975214363968001,324517315718387453247965072892240,2413138481558843201995874,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord251 : orderSearch 7 6 632589777917258855946652944772 [632589777917258855946652944772,633822886984823975214363968001,324517315718387453247965072892240,2413138481558843201995874,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord252 : orderSearch 7 6 632589777917258855946652944772 [632589777917258855946652944772,632587360074829320473452478464,633822886984823975214363968001,324517315718387453247965072892240,2413138481558843201995874,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord253 : orderSearch 7 6 632589777917258855946652944772 [632589777917258855946652944772,2417842429535473200466308,633822886984823975214363968001,324517315718387453247965072892240,2413138481558843201995874,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord254 : orderSearch 7 6 632589777917258855946652944772 [632589777917258855946652944772,632587360074829320473452478464,2417842429535473200466308,633822886984823975214363968001,324517315718387453247965072892240,2413138481558843201995874,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord255 : orderSearch 7 7 0 [0,323885963880500264155966194405544,633822886984823975214363968001,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord256 : orderSearch 7 7 0 [0,632587360074829320473452478464,323885963880500264155966194405544,633822886984823975214363968001,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord257 : orderSearch 7 6 324518551240575093476439646884008 [324518551240575093476439646884008,633822886984823975214363968001,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord258 : orderSearch 7 6 324518551240575093476439646884008 [324518551240575093476439646884008,632587360074829320473452478464,633822886984823975214363968001,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord259 : orderSearch 7 6 324518551240575093476439646884008 [324518551240575093476439646884008,323885963880500264155966194405544,633822886984823975214363968001,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord260 : orderSearch 7 6 324518551240575093476439646884008 [324518551240575093476439646884008,632587360074829320473452478464,323885963880500264155966194405544,633822886984823975214363968001,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord261 : orderSearch 7 7 324518551245297447902705984381777 [324518551245297447902705984381777,633822886984823975214363968001,632587360074829320473452478464,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord262 : orderSearch 7 7 324518551245297447902705984381777 [324518551245297447902705984381777,633822886984823975214363968001,324517315718387453247965072892240,632587360074829320473452478464,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord263 : orderSearch 7 7 633825300114100176419220670051 [633825300114100176419220670051,633822886984823975214363968001,2413138481558843201995874,632587360074829320473452478464,324517315718387453247965072892240,2417842429535473200466308,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord264 : orderSearch 7 7 633825300114110399854773996421 [633825300114110399854773996421,633822886984823975214363968001,2417842429535473200466308,632587360074829320473452478464,324517315718387453247965072892240,2413138481558843201995874,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord265 : orderSearch 7 7 324518551245297441980164008661673 [324518551245297441980164008661673,633822886984823975214363968001,323885963880500264155966194405544,632587360074829320473452478464,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord266 : orderSearch 7 7 324517318131525932550601807947122 [324517318131525932550601807947122,324517315718387453247965072892240,2413138481558843201995874,632587360074829320473452478464,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord267 : orderSearch 7 7 324517318136229873758612405594580 [324517318136229873758612405594580,324517315718387453247965072892240,2417842429535473200466308,632587360074829320473452478464,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord268 : orderSearch 7 7 323884728358312612082407668973568 [323884728358312612082407668973568,323885963880500264155966194405544,632587360074829320473452478464,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord269 : orderSearch 7 7 323884728358312612082407668973568 [323884728358312612082407668973568,324517315718387453247965072892240,323885963880500264155966194405544,632587360074829320473452478464,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord270 : orderSearch 7 7 324518551240575105321523598324216 [324518551240575105321523598324216,324517315718387453247965072892240,323885963880500264155966194405544,632587360074829320473452478464,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord271 : orderSearch 7 7 323885966293638744586706162930922 [323885966293638744586706162930922,2413138481558843201995874,323885963880500264155966194405544,632587360074829320473452478464,633822886984823975214363968001,324517315718387453247965072892240,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord272 : orderSearch 7 7 323885966298342689179026460989868 [323885966298342689179026460989868,2417842429535473200466308,323885963880500264155966194405544,632587360074829320473452478464,633822886984823975214363968001,324517315718387453247965072892240,2413138481558843201995874] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord273 : orderSearch 8 8 632587360074829320473452478464 [632587360074829320473452478464,633822886984823975214363968001,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544] = false := by
  apply ocover_step (states := [(7,0,[0,2413138481558843201995874,633822886984823975214363968001,324517315718387453247965072892240,2417842429535473200466308,323885963880500264155966194405544]),(7,0,[0,632587360074829320473452478464,2413138481558843201995874,633822886984823975214363968001,324517315718387453247965072892240,2417842429535473200466308,323885963880500264155966194405544]),(6,632589773213310879316654474338,[632589773213310879316654474338,633822886984823975214363968001,324517315718387453247965072892240,2417842429535473200466308,323885963880500264155966194405544]),(6,632589773213310879316654474338,[632589773213310879316654474338,632587360074829320473452478464,633822886984823975214363968001,324517315718387453247965072892240,2417842429535473200466308,323885963880500264155966194405544]),(6,632589773213310879316654474338,[632589773213310879316654474338,2413138481558843201995874,633822886984823975214363968001,324517315718387453247965072892240,2417842429535473200466308,323885963880500264155966194405544]),(6,632589773213310879316654474338,[632589773213310879316654474338,632587360074829320473452478464,2413138481558843201995874,633822886984823975214363968001,324517315718387453247965072892240,2417842429535473200466308,323885963880500264155966194405544]),(7,0,[0,2417842429535473200466308,633822886984823975214363968001,324517315718387453247965072892240,2413138481558843201995874,323885963880500264155966194405544]),(7,0,[0,632587360074829320473452478464,2417842429535473200466308,633822886984823975214363968001,324517315718387453247965072892240,2413138481558843201995874,323885963880500264155966194405544]),(6,632589777917258855946652944772,[632589777917258855946652944772,633822886984823975214363968001,324517315718387453247965072892240,2413138481558843201995874,323885963880500264155966194405544]),(6,632589777917258855946652944772,[632589777917258855946652944772,632587360074829320473452478464,633822886984823975214363968001,324517315718387453247965072892240,2413138481558843201995874,323885963880500264155966194405544]),(6,632589777917258855946652944772,[632589777917258855946652944772,2417842429535473200466308,633822886984823975214363968001,324517315718387453247965072892240,2413138481558843201995874,323885963880500264155966194405544]),(6,632589777917258855946652944772,[632589777917258855946652944772,632587360074829320473452478464,2417842429535473200466308,633822886984823975214363968001,324517315718387453247965072892240,2413138481558843201995874,323885963880500264155966194405544]),(7,0,[0,323885963880500264155966194405544,633822886984823975214363968001,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308]),(7,0,[0,632587360074829320473452478464,323885963880500264155966194405544,633822886984823975214363968001,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308]),(6,324518551240575093476439646884008,[324518551240575093476439646884008,633822886984823975214363968001,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308]),(6,324518551240575093476439646884008,[324518551240575093476439646884008,632587360074829320473452478464,633822886984823975214363968001,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308]),(6,324518551240575093476439646884008,[324518551240575093476439646884008,323885963880500264155966194405544,633822886984823975214363968001,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308]),(6,324518551240575093476439646884008,[324518551240575093476439646884008,632587360074829320473452478464,323885963880500264155966194405544,633822886984823975214363968001,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308]),(7,324518551245297447902705984381777,[324518551245297447902705984381777,633822886984823975214363968001,632587360074829320473452478464,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544]),(7,324518551245297447902705984381777,[324518551245297447902705984381777,633822886984823975214363968001,324517315718387453247965072892240,632587360074829320473452478464,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544]),(7,633825300114100176419220670051,[633825300114100176419220670051,633822886984823975214363968001,2413138481558843201995874,632587360074829320473452478464,324517315718387453247965072892240,2417842429535473200466308,323885963880500264155966194405544]),(7,633825300114110399854773996421,[633825300114110399854773996421,633822886984823975214363968001,2417842429535473200466308,632587360074829320473452478464,324517315718387453247965072892240,2413138481558843201995874,323885963880500264155966194405544]),(7,324518551245297441980164008661673,[324518551245297441980164008661673,633822886984823975214363968001,323885963880500264155966194405544,632587360074829320473452478464,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308]),(7,324517318131525932550601807947122,[324517318131525932550601807947122,324517315718387453247965072892240,2413138481558843201995874,632587360074829320473452478464,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544]),(7,324517318136229873758612405594580,[324517318136229873758612405594580,324517315718387453247965072892240,2417842429535473200466308,632587360074829320473452478464,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544]),(7,323884728358312612082407668973568,[323884728358312612082407668973568,323885963880500264155966194405544,632587360074829320473452478464,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308]),(7,323884728358312612082407668973568,[323884728358312612082407668973568,324517315718387453247965072892240,323885963880500264155966194405544,632587360074829320473452478464,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308]),(7,324518551240575105321523598324216,[324518551240575105321523598324216,324517315718387453247965072892240,323885963880500264155966194405544,632587360074829320473452478464,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308]),(7,323885966293638744586706162930922,[323885966293638744586706162930922,2413138481558843201995874,323885963880500264155966194405544,632587360074829320473452478464,633822886984823975214363968001,324517315718387453247965072892240,2417842429535473200466308]),(7,323885966298342689179026460989868,[323885966298342689179026460989868,2417842429535473200466308,323885963880500264155966194405544,632587360074829320473452478464,633822886984823975214363968001,324517315718387453247965072892240,2413138481558843201995874])])
  · decide +kernel
  · simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.not_false, ord243, ord244, ord245, ord246, ord247, ord248, ord249, ord250, ord251, ord252, ord253, ord254, ord255, ord256, ord257, ord258, ord259, ord260, ord261, ord262, ord263, ord264, ord265, ord266, ord267, ord268, ord269, ord270, ord271, ord272]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord274 : orderSearch 7 7 9207613844812234816 [9207613844812234816,2413138481558843201995874,633822886984823975214363968001,324517315718387453247965072892240,2417842429535473200466308,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord275 : orderSearch 7 7 9207613844812234816 [9207613844812234816,324518551245297447902705984381777,2413138481558843201995874,633822886984823975214363968001,324517315718387453247965072892240,2417842429535473200466308,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord276 : orderSearch 7 7 324518553658426721847704374142835 [324518553658426721847704374142835,2413138481558843201995874,633822886984823975214363968001,324517315718387453247965072892240,2417842429535473200466308,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord277 : orderSearch 7 7 324518553658426721847704374142835 [324518553658426721847704374142835,324518551245297447902705984381777,2413138481558843201995874,633822886984823975214363968001,324517315718387453247965072892240,2417842429535473200466308,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord278 : orderSearch 7 7 4713152135658658201856 [4713152135658658201856,2417842429535473200466308,633822886984823975214363968001,324517315718387453247965072892240,2413138481558843201995874,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord279 : orderSearch 7 7 4713152135658658201856 [4713152135658658201856,324518551245297447902705984381777,2417842429535473200466308,633822886984823975214363968001,324517315718387453247965072892240,2413138481558843201995874,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord280 : orderSearch 7 7 324518553658426725302520526646229 [324518553658426725302520526646229,2417842429535473200466308,633822886984823975214363968001,324517315718387453247965072892240,2413138481558843201995874,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord281 : orderSearch 7 7 324518553658426725302520526646229 [324518553658426725302520526646229,324518551245297447902705984381777,2417842429535473200466308,633822886984823975214363968001,324517315718387453247965072892240,2413138481558843201995874,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord282 : orderSearch 7 7 323885963880500258233424218685440 [323885963880500258233424218685440,633822886984823975214363968001,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord283 : orderSearch 7 7 323885963880500258233424218685440 [323885963880500258233424218685440,324518551245297447902705984381777,633822886984823975214363968001,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord284 : orderSearch 7 7 323885963880500258233424218685440 [323885963880500258233424218685440,323885963880500264155966194405544,633822886984823975214363968001,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord285 : orderSearch 7 7 323885963880500258233424218685440 [323885963880500258233424218685440,324518551245297447902705984381777,323885963880500264155966194405544,633822886984823975214363968001,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord286 : orderSearch 7 7 324518551245297453825247960101881 [324518551245297453825247960101881,323885963880500264155966194405544,633822886984823975214363968001,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord287 : orderSearch 7 7 324518551245297453825247960101881 [324518551245297453825247960101881,324518551245297447902705984381777,323885963880500264155966194405544,633822886984823975214363968001,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord288 : orderSearch 8 8 324518551245297447902705984381777 [324518551245297447902705984381777,633822886984823975214363968001,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544] = false := by
  apply ocover_step (states := [(7,9207613844812234816,[9207613844812234816,2413138481558843201995874,633822886984823975214363968001,324517315718387453247965072892240,2417842429535473200466308,323885963880500264155966194405544]),(7,9207613844812234816,[9207613844812234816,324518551245297447902705984381777,2413138481558843201995874,633822886984823975214363968001,324517315718387453247965072892240,2417842429535473200466308,323885963880500264155966194405544]),(7,324518553658426721847704374142835,[324518553658426721847704374142835,2413138481558843201995874,633822886984823975214363968001,324517315718387453247965072892240,2417842429535473200466308,323885963880500264155966194405544]),(7,324518553658426721847704374142835,[324518553658426721847704374142835,324518551245297447902705984381777,2413138481558843201995874,633822886984823975214363968001,324517315718387453247965072892240,2417842429535473200466308,323885963880500264155966194405544]),(7,4713152135658658201856,[4713152135658658201856,2417842429535473200466308,633822886984823975214363968001,324517315718387453247965072892240,2413138481558843201995874,323885963880500264155966194405544]),(7,4713152135658658201856,[4713152135658658201856,324518551245297447902705984381777,2417842429535473200466308,633822886984823975214363968001,324517315718387453247965072892240,2413138481558843201995874,323885963880500264155966194405544]),(7,324518553658426725302520526646229,[324518553658426725302520526646229,2417842429535473200466308,633822886984823975214363968001,324517315718387453247965072892240,2413138481558843201995874,323885963880500264155966194405544]),(7,324518553658426725302520526646229,[324518553658426725302520526646229,324518551245297447902705984381777,2417842429535473200466308,633822886984823975214363968001,324517315718387453247965072892240,2413138481558843201995874,323885963880500264155966194405544]),(7,323885963880500258233424218685440,[323885963880500258233424218685440,633822886984823975214363968001,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308]),(7,323885963880500258233424218685440,[323885963880500258233424218685440,324518551245297447902705984381777,633822886984823975214363968001,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308]),(7,323885963880500258233424218685440,[323885963880500258233424218685440,323885963880500264155966194405544,633822886984823975214363968001,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308]),(7,323885963880500258233424218685440,[323885963880500258233424218685440,324518551245297447902705984381777,323885963880500264155966194405544,633822886984823975214363968001,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308]),(7,324518551245297453825247960101881,[324518551245297453825247960101881,323885963880500264155966194405544,633822886984823975214363968001,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308]),(7,324518551245297453825247960101881,[324518551245297453825247960101881,324518551245297447902705984381777,323885963880500264155966194405544,633822886984823975214363968001,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308])])
  · decide +kernel
  · simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.not_false, ord274, ord275, ord276, ord277, ord278, ord279, ord280, ord281, ord282, ord283, ord284, ord285, ord286, ord287]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord289 : orderSearch 7 7 0 [0,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord290 : orderSearch 7 7 0 [0,2413129272746388704198656,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord291 : orderSearch 7 6 633825300114096721603068166657 [633825300114096721603068166657,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord292 : orderSearch 7 6 633825300114096721603068166657 [633825300114096721603068166657,2413129272746388704198656,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord293 : orderSearch 7 6 633825300114096721603068166657 [633825300114096721603068166657,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord294 : orderSearch 7 6 633825300114096721603068166657 [633825300114096721603068166657,2413129272746388704198656,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord295 : orderSearch 7 7 0 [0,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord296 : orderSearch 7 7 0 [0,2413129272746388704198656,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord297 : orderSearch 7 6 323885966293629536902354898604200 [323885966293629536902354898604200,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord298 : orderSearch 7 6 323885966293629536902354898604200 [323885966293629536902354898604200,2413129272746388704198656,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord299 : orderSearch 7 6 323885966293629536902354898604200 [323885966293629536902354898604200,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord300 : orderSearch 7 6 323885966293629536902354898604200 [323885966293629536902354898604200,2413129272746388704198656,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord301 : orderSearch 7 7 0 [0,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord302 : orderSearch 7 7 0 [0,2413129272746388704198656,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord303 : orderSearch 7 6 324517318131516725994353777090896 [324517318131516725994353777090896,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord304 : orderSearch 7 6 324517318131516725994353777090896 [324517318131516725994353777090896,2413129272746388704198656,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord305 : orderSearch 7 6 324517318131516725994353777090896 [324517318131516725994353777090896,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord306 : orderSearch 7 6 324517318131516725994353777090896 [324517318131516725994353777090896,2413129272746388704198656,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord307 : orderSearch 6 6 4722348468471135731712 [4722348468471135731712,633822886984823975214363968001,2413129272746388704198656,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord308 : orderSearch 6 6 4722348468471135731712 [4722348468471135731712,2417851638347927698263526,633822886984823975214363968001,2413129272746388704198656,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord309 : orderSearch 6 6 633825300114113854670926499815 [633825300114113854670926499815,2417851638347927698263526,633822886984823975214363968001,2413129272746388704198656,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord310 : orderSearch 6 6 5640516167352480 [5640516167352480,2417851638347927698263526,323885963880500264155966194405544,2413129272746388704198656,633822886984823975214363968001,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord311 : orderSearch 6 6 323885966298351896863377725316590 [323885966298351896863377725316590,323885963880500264155966194405544,2413129272746388704198656,633822886984823975214363968001,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord312 : orderSearch 6 6 323885966298351896863377725316590 [323885966298351896863377725316590,2417851638347927698263526,323885963880500264155966194405544,2413129272746388704198656,633822886984823975214363968001,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord313 : orderSearch 6 6 11281032334704960 [11281032334704960,2417851638347927698263526,324517315718387453247965072892240,2413129272746388704198656,633822886984823975214363968001,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord314 : orderSearch 6 6 324517318136239080314860436450806 [324517318136239080314860436450806,324517315718387453247965072892240,2413129272746388704198656,633822886984823975214363968001,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord315 : orderSearch 6 6 324517318136239080314860436450806 [324517318136239080314860436450806,2417851638347927698263526,324517315718387453247965072892240,2413129272746388704198656,633822886984823975214363968001,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord316 : orderSearch 6 5 633825300114096721603068166657 [633825300114096721603068166657,2417851638347927698263526,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord317 : orderSearch 6 5 633825300114096721603068166657 [633825300114096721603068166657,2413129272746388704198656,2417851638347927698263526,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord318 : orderSearch 6 5 633825300114096721603068166657 [633825300114096721603068166657,633822886984823975214363968001,2417851638347927698263526,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord319 : orderSearch 6 5 633825300114096721603068166657 [633825300114096721603068166657,2413129272746388704198656,633822886984823975214363968001,2417851638347927698263526,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord320 : orderSearch 6 5 323885966293629536902354898604200 [323885966293629536902354898604200,2413129272746388704198656,2417851638347927698263526,633822886984823975214363968001,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord321 : orderSearch 6 5 323885966293629536902354898604200 [323885966293629536902354898604200,2413129272746388704198656,323885963880500264155966194405544,2417851638347927698263526,633822886984823975214363968001,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord322 : orderSearch 6 5 324517318131516725994353777090896 [324517318131516725994353777090896,2413129272746388704198656,2417851638347927698263526,633822886984823975214363968001,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord323 : orderSearch 6 5 324517318131516725994353777090896 [324517318131516725994353777090896,2413129272746388704198656,324517315718387453247965072892240,2417851638347927698263526,633822886984823975214363968001,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord324 : orderSearch 6 6 1235522187646151016549711872 [1235522187646151016549711872,633822886984823975214363968001,323885963880500264155966194405544,2417851638347927698263526,2413129272746388704198656,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord325 : orderSearch 6 6 324518551245297441980164008661673 [324518551245297441980164008661673,633822886984823975214363968001,323885963880500264155966194405544,2417851638347927698263526,2413129272746388704198656,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord326 : orderSearch 6 6 632587360074829320473452478464 [632587360074829320473452478464,633822886984823975214363968001,324517315718387453247965072892240,2417851638347927698263526,2413129272746388704198656,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord327 : orderSearch 6 6 324518551245297447902705984381777 [324518551245297447902705984381777,633822886984823975214363968001,324517315718387453247965072892240,2417851638347927698263526,2413129272746388704198656,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord328 : orderSearch 6 6 323884728358312612082407668973568 [323884728358312612082407668973568,323885963880500264155966194405544,324517315718387453247965072892240,2417851638347927698263526,2413129272746388704198656,633822886984823975214363968001] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord329 : orderSearch 6 6 324518551240575105321523598324216 [324518551240575105321523598324216,323885963880500264155966194405544,324517315718387453247965072892240,2417851638347927698263526,2413129272746388704198656,633822886984823975214363968001] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord330 : orderSearch 7 7 2417851638347927698263526 [2417851638347927698263526,2413129272746388704198656,633822886984823975214363968001,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  apply ocover_step (states := [(6,4722348468471135731712,[4722348468471135731712,633822886984823975214363968001,2413129272746388704198656,323885963880500264155966194405544,324517315718387453247965072892240]),(6,4722348468471135731712,[4722348468471135731712,2417851638347927698263526,633822886984823975214363968001,2413129272746388704198656,323885963880500264155966194405544,324517315718387453247965072892240]),(6,633825300114113854670926499815,[633825300114113854670926499815,2417851638347927698263526,633822886984823975214363968001,2413129272746388704198656,323885963880500264155966194405544,324517315718387453247965072892240]),(6,5640516167352480,[5640516167352480,2417851638347927698263526,323885963880500264155966194405544,2413129272746388704198656,633822886984823975214363968001,324517315718387453247965072892240]),(6,323885966298351896863377725316590,[323885966298351896863377725316590,323885963880500264155966194405544,2413129272746388704198656,633822886984823975214363968001,324517315718387453247965072892240]),(6,323885966298351896863377725316590,[323885966298351896863377725316590,2417851638347927698263526,323885963880500264155966194405544,2413129272746388704198656,633822886984823975214363968001,324517315718387453247965072892240]),(6,11281032334704960,[11281032334704960,2417851638347927698263526,324517315718387453247965072892240,2413129272746388704198656,633822886984823975214363968001,323885963880500264155966194405544]),(6,324517318136239080314860436450806,[324517318136239080314860436450806,324517315718387453247965072892240,2413129272746388704198656,633822886984823975214363968001,323885963880500264155966194405544]),(6,324517318136239080314860436450806,[324517318136239080314860436450806,2417851638347927698263526,324517315718387453247965072892240,2413129272746388704198656,633822886984823975214363968001,323885963880500264155966194405544]),(5,633825300114096721603068166657,[633825300114096721603068166657,2417851638347927698263526,323885963880500264155966194405544,324517315718387453247965072892240]),(5,633825300114096721603068166657,[633825300114096721603068166657,2413129272746388704198656,2417851638347927698263526,323885963880500264155966194405544,324517315718387453247965072892240]),(5,633825300114096721603068166657,[633825300114096721603068166657,633822886984823975214363968001,2417851638347927698263526,323885963880500264155966194405544,324517315718387453247965072892240]),(5,633825300114096721603068166657,[633825300114096721603068166657,2413129272746388704198656,633822886984823975214363968001,2417851638347927698263526,323885963880500264155966194405544,324517315718387453247965072892240]),(5,323885966293629536902354898604200,[323885966293629536902354898604200,2413129272746388704198656,2417851638347927698263526,633822886984823975214363968001,324517315718387453247965072892240]),(5,323885966293629536902354898604200,[323885966293629536902354898604200,2413129272746388704198656,323885963880500264155966194405544,2417851638347927698263526,633822886984823975214363968001,324517315718387453247965072892240]),(5,324517318131516725994353777090896,[324517318131516725994353777090896,2413129272746388704198656,2417851638347927698263526,633822886984823975214363968001,323885963880500264155966194405544]),(5,324517318131516725994353777090896,[324517318131516725994353777090896,2413129272746388704198656,324517315718387453247965072892240,2417851638347927698263526,633822886984823975214363968001,323885963880500264155966194405544]),(6,1235522187646151016549711872,[1235522187646151016549711872,633822886984823975214363968001,323885963880500264155966194405544,2417851638347927698263526,2413129272746388704198656,324517315718387453247965072892240]),(6,324518551245297441980164008661673,[324518551245297441980164008661673,633822886984823975214363968001,323885963880500264155966194405544,2417851638347927698263526,2413129272746388704198656,324517315718387453247965072892240]),(6,632587360074829320473452478464,[632587360074829320473452478464,633822886984823975214363968001,324517315718387453247965072892240,2417851638347927698263526,2413129272746388704198656,323885963880500264155966194405544]),(6,324518551245297447902705984381777,[324518551245297447902705984381777,633822886984823975214363968001,324517315718387453247965072892240,2417851638347927698263526,2413129272746388704198656,323885963880500264155966194405544]),(6,323884728358312612082407668973568,[323884728358312612082407668973568,323885963880500264155966194405544,324517315718387453247965072892240,2417851638347927698263526,2413129272746388704198656,633822886984823975214363968001]),(6,324518551240575105321523598324216,[324518551240575105321523598324216,323885963880500264155966194405544,324517315718387453247965072892240,2417851638347927698263526,2413129272746388704198656,633822886984823975214363968001])])
  · decide +kernel
  · simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.not_false, ord307, ord308, ord309, ord310, ord311, ord312, ord313, ord314, ord315, ord316, ord317, ord318, ord319, ord320, ord321, ord322, ord323, ord324, ord325, ord326, ord327, ord328, ord329]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord331 : orderSearch 7 7 2417851638347927698263526 [2417851638347927698263526,2413138481558843201995874,2413129272746388704198656,633822886984823975214363968001,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord332 : orderSearch 7 7 2417851638347927698263526 [2417851638347927698263526,2417842429535473200466308,2413129272746388704198656,633822886984823975214363968001,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord333 : orderSearch 7 7 2417851638347927698263526 [2417851638347927698263526,2413138481558843201995874,2417842429535473200466308,2413129272746388704198656,633822886984823975214363968001,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord334 : orderSearch 7 7 633825300114100176419220670051 [633825300114100176419220670051,2413138481558843201995874,633822886984823975214363968001,2413129272746388704198656,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord335 : orderSearch 7 7 323885966293638744586706162930922 [323885966293638744586706162930922,323885963880500264155966194405544,2413129272746388704198656,2417842429535473200466308,633822886984823975214363968001,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord336 : orderSearch 7 7 323885966293638744586706162930922 [323885966293638744586706162930922,2413138481558843201995874,323885963880500264155966194405544,2413129272746388704198656,2417842429535473200466308,633822886984823975214363968001,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord337 : orderSearch 7 7 324517318131525932550601807947122 [324517318131525932550601807947122,324517315718387453247965072892240,2413129272746388704198656,2417842429535473200466308,633822886984823975214363968001,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord338 : orderSearch 7 7 324517318131525932550601807947122 [324517318131525932550601807947122,2413138481558843201995874,324517315718387453247965072892240,2413129272746388704198656,2417842429535473200466308,633822886984823975214363968001,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord339 : orderSearch 7 7 633825300114110399854773996421 [633825300114110399854773996421,2417842429535473200466308,633822886984823975214363968001,2413129272746388704198656,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord340 : orderSearch 7 7 323885966298342689179026460989868 [323885966298342689179026460989868,323885963880500264155966194405544,2413129272746388704198656,2413138481558843201995874,633822886984823975214363968001,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord341 : orderSearch 7 7 323885966298342689179026460989868 [323885966298342689179026460989868,2417842429535473200466308,323885963880500264155966194405544,2413129272746388704198656,2413138481558843201995874,633822886984823975214363968001,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord342 : orderSearch 7 7 324517318136229873758612405594580 [324517318136229873758612405594580,324517315718387453247965072892240,2413129272746388704198656,2413138481558843201995874,633822886984823975214363968001,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord343 : orderSearch 7 7 324517318136229873758612405594580 [324517318136229873758612405594580,2417842429535473200466308,324517315718387453247965072892240,2413129272746388704198656,2413138481558843201995874,633822886984823975214363968001,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord344 : orderSearch 7 7 1235522187646151016549711872 [1235522187646151016549711872,633822886984823975214363968001,323885963880500264155966194405544,2413129272746388704198656,2413138481558843201995874,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord345 : orderSearch 7 7 324518551245297441980164008661673 [324518551245297441980164008661673,633822886984823975214363968001,323885963880500264155966194405544,2413129272746388704198656,2413138481558843201995874,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord346 : orderSearch 7 7 632587360074829320473452478464 [632587360074829320473452478464,633822886984823975214363968001,324517315718387453247965072892240,2413129272746388704198656,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord347 : orderSearch 7 7 324518551245297447902705984381777 [324518551245297447902705984381777,633822886984823975214363968001,324517315718387453247965072892240,2413129272746388704198656,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord348 : orderSearch 6 6 0 [0,323885963880500264155966194405544,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord349 : orderSearch 6 6 0 [0,323884728358312612082407668973568,323885963880500264155966194405544,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord350 : orderSearch 6 6 0 [0,2413129272746388704198656,323885963880500264155966194405544,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord351 : orderSearch 6 5 323884730771441884828796373172224 [323884730771441884828796373172224,323885963880500264155966194405544,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord352 : orderSearch 6 6 0 [0,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240,2413129272746388704198656,2417842429535473200466308,633822886984823975214363968001] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord353 : orderSearch 6 5 323884730771451093641250870969442 [323884730771451093641250870969442,323885963880500264155966194405544,324517315718387453247965072892240,2413129272746388704198656,2417842429535473200466308,633822886984823975214363968001] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord354 : orderSearch 6 6 0 [0,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240,2413129272746388704198656,2413138481558843201995874,633822886984823975214363968001] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord355 : orderSearch 6 5 323884730776155041617880869439876 [323884730776155041617880869439876,323885963880500264155966194405544,324517315718387453247965072892240,2413129272746388704198656,2413138481558843201995874,633822886984823975214363968001] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord356 : orderSearch 6 6 0 [0,633822886984823975214363968001,323885963880500264155966194405544,324517315718387453247965072892240,2413129272746388704198656,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord357 : orderSearch 6 5 324518551245297436057622032941569 [324518551245297436057622032941569,323885963880500264155966194405544,324517315718387453247965072892240,2413129272746388704198656,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord358 : orderSearch 6 6 324518551240575105321523598324216 [324518551240575105321523598324216,323884728358312612082407668973568,2413129272746388704198656,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord359 : orderSearch 6 6 324518551240575105321523598324216 [324518551240575105321523598324216,323885963880500264155966194405544,323884728358312612082407668973568,2413129272746388704198656,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord360 : orderSearch 6 6 324518551240575105321523598324216 [324518551240575105321523598324216,324517315718387453247965072892240,323884728358312612082407668973568,2413129272746388704198656,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord361 : orderSearch 6 5 323885966293629536902354898604200 [323885966293629536902354898604200,323884728358312612082407668973568,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord362 : orderSearch 6 6 323885966293638744586706162930922 [323885966293638744586706162930922,323884728358312612082407668973568,324517315718387453247965072892240,2413129272746388704198656,2417842429535473200466308,633822886984823975214363968001] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord363 : orderSearch 6 6 323885966293638744586706162930922 [323885966293638744586706162930922,323885963880500264155966194405544,323884728358312612082407668973568,324517315718387453247965072892240,2413129272746388704198656,2417842429535473200466308,633822886984823975214363968001] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord364 : orderSearch 6 6 323885966293638744586706162930922 [323885966293638744586706162930922,2413138481558843201995874,323884728358312612082407668973568,324517315718387453247965072892240,2413129272746388704198656,2417842429535473200466308,633822886984823975214363968001] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord365 : orderSearch 6 6 323885966298342689179026460989868 [323885966298342689179026460989868,323884728358312612082407668973568,324517315718387453247965072892240,2413129272746388704198656,2413138481558843201995874,633822886984823975214363968001] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord366 : orderSearch 6 6 323885966298342689179026460989868 [323885966298342689179026460989868,323885963880500264155966194405544,323884728358312612082407668973568,324517315718387453247965072892240,2413129272746388704198656,2413138481558843201995874,633822886984823975214363968001] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord367 : orderSearch 6 6 323885966298342689179026460989868 [323885966298342689179026460989868,2417842429535473200466308,323884728358312612082407668973568,324517315718387453247965072892240,2413129272746388704198656,2413138481558843201995874,633822886984823975214363968001] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord368 : orderSearch 6 5 324517318131516725994353777090896 [324517318131516725994353777090896,323884728358312612082407668973568,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord369 : orderSearch 6 6 324517318131525932550601807947122 [324517318131525932550601807947122,323884728358312612082407668973568,323885963880500264155966194405544,2413129272746388704198656,2417842429535473200466308,633822886984823975214363968001] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord370 : orderSearch 6 6 324517318131525932550601807947122 [324517318131525932550601807947122,324517315718387453247965072892240,323884728358312612082407668973568,323885963880500264155966194405544,2413129272746388704198656,2417842429535473200466308,633822886984823975214363968001] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord371 : orderSearch 6 6 324517318131525932550601807947122 [324517318131525932550601807947122,2413138481558843201995874,323884728358312612082407668973568,323885963880500264155966194405544,2413129272746388704198656,2417842429535473200466308,633822886984823975214363968001] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord372 : orderSearch 6 6 324517318136229873758612405594580 [324517318136229873758612405594580,323884728358312612082407668973568,323885963880500264155966194405544,2413129272746388704198656,2413138481558843201995874,633822886984823975214363968001] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord373 : orderSearch 6 6 324517318136229873758612405594580 [324517318136229873758612405594580,324517315718387453247965072892240,323884728358312612082407668973568,323885963880500264155966194405544,2413129272746388704198656,2413138481558843201995874,633822886984823975214363968001] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord374 : orderSearch 6 6 324517318136229873758612405594580 [324517318136229873758612405594580,2417842429535473200466308,323884728358312612082407668973568,323885963880500264155966194405544,2413129272746388704198656,2413138481558843201995874,633822886984823975214363968001] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord375 : orderSearch 7 7 323884728358312612082407668973568 [323884728358312612082407668973568,323885963880500264155966194405544,324517315718387453247965072892240,2413129272746388704198656,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001] = false := by
  apply ocover_step (states := [(6,0,[0,323885963880500264155966194405544,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001]),(6,0,[0,323884728358312612082407668973568,323885963880500264155966194405544,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001]),(6,0,[0,2413129272746388704198656,323885963880500264155966194405544,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001]),(5,323884730771441884828796373172224,[323884730771441884828796373172224,323885963880500264155966194405544,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001]),(6,0,[0,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240,2413129272746388704198656,2417842429535473200466308,633822886984823975214363968001]),(5,323884730771451093641250870969442,[323884730771451093641250870969442,323885963880500264155966194405544,324517315718387453247965072892240,2413129272746388704198656,2417842429535473200466308,633822886984823975214363968001]),(6,0,[0,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240,2413129272746388704198656,2413138481558843201995874,633822886984823975214363968001]),(5,323884730776155041617880869439876,[323884730776155041617880869439876,323885963880500264155966194405544,324517315718387453247965072892240,2413129272746388704198656,2413138481558843201995874,633822886984823975214363968001]),(6,0,[0,633822886984823975214363968001,323885963880500264155966194405544,324517315718387453247965072892240,2413129272746388704198656,2413138481558843201995874,2417842429535473200466308]),(5,324518551245297436057622032941569,[324518551245297436057622032941569,323885963880500264155966194405544,324517315718387453247965072892240,2413129272746388704198656,2413138481558843201995874,2417842429535473200466308]),(6,324518551240575105321523598324216,[324518551240575105321523598324216,323884728358312612082407668973568,2413129272746388704198656,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001]),(6,324518551240575105321523598324216,[324518551240575105321523598324216,323885963880500264155966194405544,323884728358312612082407668973568,2413129272746388704198656,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001]),(6,324518551240575105321523598324216,[324518551240575105321523598324216,324517315718387453247965072892240,323884728358312612082407668973568,2413129272746388704198656,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001]),(5,323885966293629536902354898604200,[323885966293629536902354898604200,323884728358312612082407668973568,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001]),(6,323885966293638744586706162930922,[323885966293638744586706162930922,323884728358312612082407668973568,324517315718387453247965072892240,2413129272746388704198656,2417842429535473200466308,633822886984823975214363968001]),(6,323885966293638744586706162930922,[323885966293638744586706162930922,323885963880500264155966194405544,323884728358312612082407668973568,324517315718387453247965072892240,2413129272746388704198656,2417842429535473200466308,633822886984823975214363968001]),(6,323885966293638744586706162930922,[323885966293638744586706162930922,2413138481558843201995874,323884728358312612082407668973568,324517315718387453247965072892240,2413129272746388704198656,2417842429535473200466308,633822886984823975214363968001]),(6,323885966298342689179026460989868,[323885966298342689179026460989868,323884728358312612082407668973568,324517315718387453247965072892240,2413129272746388704198656,2413138481558843201995874,633822886984823975214363968001]),(6,323885966298342689179026460989868,[323885966298342689179026460989868,323885963880500264155966194405544,323884728358312612082407668973568,324517315718387453247965072892240,2413129272746388704198656,2413138481558843201995874,633822886984823975214363968001]),(6,323885966298342689179026460989868,[323885966298342689179026460989868,2417842429535473200466308,323884728358312612082407668973568,324517315718387453247965072892240,2413129272746388704198656,2413138481558843201995874,633822886984823975214363968001]),(5,324517318131516725994353777090896,[324517318131516725994353777090896,323884728358312612082407668973568,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001]),(6,324517318131525932550601807947122,[324517318131525932550601807947122,323884728358312612082407668973568,323885963880500264155966194405544,2413129272746388704198656,2417842429535473200466308,633822886984823975214363968001]),(6,324517318131525932550601807947122,[324517318131525932550601807947122,324517315718387453247965072892240,323884728358312612082407668973568,323885963880500264155966194405544,2413129272746388704198656,2417842429535473200466308,633822886984823975214363968001]),(6,324517318131525932550601807947122,[324517318131525932550601807947122,2413138481558843201995874,323884728358312612082407668973568,323885963880500264155966194405544,2413129272746388704198656,2417842429535473200466308,633822886984823975214363968001]),(6,324517318136229873758612405594580,[324517318136229873758612405594580,323884728358312612082407668973568,323885963880500264155966194405544,2413129272746388704198656,2413138481558843201995874,633822886984823975214363968001]),(6,324517318136229873758612405594580,[324517318136229873758612405594580,324517315718387453247965072892240,323884728358312612082407668973568,323885963880500264155966194405544,2413129272746388704198656,2413138481558843201995874,633822886984823975214363968001]),(6,324517318136229873758612405594580,[324517318136229873758612405594580,2417842429535473200466308,323884728358312612082407668973568,323885963880500264155966194405544,2413129272746388704198656,2413138481558843201995874,633822886984823975214363968001])])
  · decide +kernel
  · simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.not_false, ord348, ord349, ord350, ord351, ord352, ord353, ord354, ord355, ord356, ord357, ord358, ord359, ord360, ord361, ord362, ord363, ord364, ord365, ord366, ord367, ord368, ord369, ord370, ord371, ord372, ord373, ord374]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord376 : orderSearch 7 7 324518551240575105321523598324216 [324518551240575105321523598324216,323885963880500264155966194405544,324517315718387453247965072892240,2413129272746388704198656,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord377 : orderSearch 8 8 2413129272746388704198656 [2413129272746388704198656,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  apply ocover_step (states := [(7,0,[0,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240]),(7,0,[0,2413129272746388704198656,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240]),(6,633825300114096721603068166657,[633825300114096721603068166657,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240]),(6,633825300114096721603068166657,[633825300114096721603068166657,2413129272746388704198656,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240]),(6,633825300114096721603068166657,[633825300114096721603068166657,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240]),(6,633825300114096721603068166657,[633825300114096721603068166657,2413129272746388704198656,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240]),(7,0,[0,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001,324517315718387453247965072892240]),(7,0,[0,2413129272746388704198656,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001,324517315718387453247965072892240]),(6,323885966293629536902354898604200,[323885966293629536902354898604200,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001,324517315718387453247965072892240]),(6,323885966293629536902354898604200,[323885966293629536902354898604200,2413129272746388704198656,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001,324517315718387453247965072892240]),(6,323885966293629536902354898604200,[323885966293629536902354898604200,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001,324517315718387453247965072892240]),(6,323885966293629536902354898604200,[323885966293629536902354898604200,2413129272746388704198656,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001,324517315718387453247965072892240]),(7,0,[0,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001,323885963880500264155966194405544]),(7,0,[0,2413129272746388704198656,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001,323885963880500264155966194405544]),(6,324517318131516725994353777090896,[324517318131516725994353777090896,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001,323885963880500264155966194405544]),(6,324517318131516725994353777090896,[324517318131516725994353777090896,2413129272746388704198656,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001,323885963880500264155966194405544]),(6,324517318131516725994353777090896,[324517318131516725994353777090896,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001,323885963880500264155966194405544]),(6,324517318131516725994353777090896,[324517318131516725994353777090896,2413129272746388704198656,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001,323885963880500264155966194405544]),(7,2417851638347927698263526,[2417851638347927698263526,2413129272746388704198656,633822886984823975214363968001,323885963880500264155966194405544,324517315718387453247965072892240]),(7,2417851638347927698263526,[2417851638347927698263526,2413138481558843201995874,2413129272746388704198656,633822886984823975214363968001,323885963880500264155966194405544,324517315718387453247965072892240]),(7,2417851638347927698263526,[2417851638347927698263526,2417842429535473200466308,2413129272746388704198656,633822886984823975214363968001,323885963880500264155966194405544,324517315718387453247965072892240]),(7,2417851638347927698263526,[2417851638347927698263526,2413138481558843201995874,2417842429535473200466308,2413129272746388704198656,633822886984823975214363968001,323885963880500264155966194405544,324517315718387453247965072892240]),(7,633825300114100176419220670051,[633825300114100176419220670051,2413138481558843201995874,633822886984823975214363968001,2413129272746388704198656,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240]),(7,323885966293638744586706162930922,[323885966293638744586706162930922,323885963880500264155966194405544,2413129272746388704198656,2417842429535473200466308,633822886984823975214363968001,324517315718387453247965072892240]),(7,323885966293638744586706162930922,[323885966293638744586706162930922,2413138481558843201995874,323885963880500264155966194405544,2413129272746388704198656,2417842429535473200466308,633822886984823975214363968001,324517315718387453247965072892240]),(7,324517318131525932550601807947122,[324517318131525932550601807947122,324517315718387453247965072892240,2413129272746388704198656,2417842429535473200466308,633822886984823975214363968001,323885963880500264155966194405544]),(7,324517318131525932550601807947122,[324517318131525932550601807947122,2413138481558843201995874,324517315718387453247965072892240,2413129272746388704198656,2417842429535473200466308,633822886984823975214363968001,323885963880500264155966194405544]),(7,633825300114110399854773996421,[633825300114110399854773996421,2417842429535473200466308,633822886984823975214363968001,2413129272746388704198656,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240]),(7,323885966298342689179026460989868,[323885966298342689179026460989868,323885963880500264155966194405544,2413129272746388704198656,2413138481558843201995874,633822886984823975214363968001,324517315718387453247965072892240]),(7,323885966298342689179026460989868,[323885966298342689179026460989868,2417842429535473200466308,323885963880500264155966194405544,2413129272746388704198656,2413138481558843201995874,633822886984823975214363968001,324517315718387453247965072892240]),(7,324517318136229873758612405594580,[324517318136229873758612405594580,324517315718387453247965072892240,2413129272746388704198656,2413138481558843201995874,633822886984823975214363968001,323885963880500264155966194405544]),(7,324517318136229873758612405594580,[324517318136229873758612405594580,2417842429535473200466308,324517315718387453247965072892240,2413129272746388704198656,2413138481558843201995874,633822886984823975214363968001,323885963880500264155966194405544]),(7,1235522187646151016549711872,[1235522187646151016549711872,633822886984823975214363968001,323885963880500264155966194405544,2413129272746388704198656,2413138481558843201995874,2417842429535473200466308,324517315718387453247965072892240]),(7,324518551245297441980164008661673,[324518551245297441980164008661673,633822886984823975214363968001,323885963880500264155966194405544,2413129272746388704198656,2413138481558843201995874,2417842429535473200466308,324517315718387453247965072892240]),(7,632587360074829320473452478464,[632587360074829320473452478464,633822886984823975214363968001,324517315718387453247965072892240,2413129272746388704198656,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544]),(7,324518551245297447902705984381777,[324518551245297447902705984381777,633822886984823975214363968001,324517315718387453247965072892240,2413129272746388704198656,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544]),(7,323884728358312612082407668973568,[323884728358312612082407668973568,323885963880500264155966194405544,324517315718387453247965072892240,2413129272746388704198656,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001]),(7,324518551240575105321523598324216,[324518551240575105321523598324216,323885963880500264155966194405544,324517315718387453247965072892240,2413129272746388704198656,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001])])
  · decide +kernel
  · simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.not_false, ord289, ord290, ord291, ord292, ord293, ord294, ord295, ord296, ord297, ord298, ord299, ord300, ord301, ord302, ord303, ord304, ord305, ord306, ord330, ord331, ord332, ord333, ord334, ord335, ord336, ord337, ord338, ord339, ord340, ord341, ord342, ord343, ord344, ord345, ord346, ord347, ord375, ord376]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord378 : orderSearch 7 7 4722348468471135731712 [4722348468471135731712,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord379 : orderSearch 7 7 4722348468471135731712 [4722348468471135731712,2417851638347927698263526,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord380 : orderSearch 7 7 633825300114113854670926499815 [633825300114113854670926499815,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord381 : orderSearch 7 7 633825300114113854670926499815 [633825300114113854670926499815,2417851638347927698263526,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord382 : orderSearch 7 7 5640516167352480 [5640516167352480,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord383 : orderSearch 7 7 5640516167352480 [5640516167352480,2417851638347927698263526,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord384 : orderSearch 7 7 323885966298351896863377725316590 [323885966298351896863377725316590,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord385 : orderSearch 7 7 323885966298351896863377725316590 [323885966298351896863377725316590,2417851638347927698263526,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord386 : orderSearch 7 7 11281032334704960 [11281032334704960,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord387 : orderSearch 7 7 11281032334704960 [11281032334704960,2417851638347927698263526,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord388 : orderSearch 7 7 324517318136239080314860436450806 [324517318136239080314860436450806,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord389 : orderSearch 7 7 324517318136239080314860436450806 [324517318136239080314860436450806,2417851638347927698263526,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord390 : orderSearch 6 6 2417851624669675992433762 [2417851624669675992433762,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord391 : orderSearch 6 6 2417851624669675992433762 [2417851624669675992433762,633825300114100176419220670051,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord392 : orderSearch 6 6 2417851624669675992433762 [2417851624669675992433762,2417851638347927698263526,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord393 : orderSearch 6 6 2417851624669675992433762 [2417851624669675992433762,633825300114100176419220670051,2417851638347927698263526,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord394 : orderSearch 6 6 633825300114113854670926499815 [633825300114113854670926499815,633825300114100176419220670051,2417851638347927698263526,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord395 : orderSearch 6 6 2417842415857221494636544 [2417842415857221494636544,633822886984823975214363968001,2417851638347927698263526,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord396 : orderSearch 6 6 2417842415857221494636544 [2417842415857221494636544,633825300114100176419220670051,633822886984823975214363968001,2417851638347927698263526,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord397 : orderSearch 6 6 2417842415857221494636544 [2417842415857221494636544,2417842429535473200466308,633822886984823975214363968001,2417851638347927698263526,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord398 : orderSearch 6 6 2417842415857221494636544 [2417842415857221494636544,633825300114100176419220670051,2417842429535473200466308,633822886984823975214363968001,2417851638347927698263526,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord399 : orderSearch 6 6 633825300114113854670926499815 [633825300114113854670926499815,633825300114100176419220670051,2417842429535473200466308,633822886984823975214363968001,2417851638347927698263526,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord400 : orderSearch 6 6 1235522187647279119783182368 [1235522187647279119783182368,633825300114100176419220670051,323885963880500264155966194405544,633822886984823975214363968001,2417851638347927698263526,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord401 : orderSearch 6 6 324518553658426717053265631893227 [324518553658426717053265631893227,633825300114100176419220670051,323885963880500264155966194405544,633822886984823975214363968001,2417851638347927698263526,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord402 : orderSearch 6 6 632587360074831576679919419456 [632587360074831576679919419456,633825300114100176419220670051,324517315718387453247965072892240,633822886984823975214363968001,2417851638347927698263526,2417842429535473200466308,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord403 : orderSearch 6 6 324518553658426721847704374142835 [324518553658426721847704374142835,633825300114100176419220670051,324517315718387453247965072892240,633822886984823975214363968001,2417851638347927698263526,2417842429535473200466308,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord404 : orderSearch 6 6 633825300114113854670926499815 [633825300114113854670926499815,633822886984823975214363968001,2417851638347927698263526,633825300114100176419220670051,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord405 : orderSearch 6 6 633825300114110399854773996421 [633825300114110399854773996421,633825300114100176419220670051,2417851638347927698263526,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord406 : orderSearch 6 6 633825300114110399854773996421 [633825300114110399854773996421,633822886984823975214363968001,633825300114100176419220670051,2417851638347927698263526,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord407 : orderSearch 6 6 633825300114110399854773996421 [633825300114110399854773996421,2417842429535473200466308,633825300114100176419220670051,2417851638347927698263526,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord408 : orderSearch 6 6 633825300114110399854773996421 [633825300114110399854773996421,633822886984823975214363968001,2417842429535473200466308,633825300114100176419220670051,2417851638347927698263526,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord409 : orderSearch 6 6 324518551245297441980164008661673 [324518551245297441980164008661673,633822886984823975214363968001,323885963880500264155966194405544,633825300114100176419220670051,2417851638347927698263526,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord410 : orderSearch 6 6 324518551245297447902705984381777 [324518551245297447902705984381777,633822886984823975214363968001,324517315718387453247965072892240,633825300114100176419220670051,2417851638347927698263526,2417842429535473200466308,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord411 : orderSearch 6 6 323885966298351896863377725316590 [323885966298351896863377725316590,323885963880500264155966194405544,633825300114100176419220670051,633822886984823975214363968001,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord412 : orderSearch 6 6 323885966298351896863377725316590 [323885966298351896863377725316590,2417851638347927698263526,323885963880500264155966194405544,633825300114100176419220670051,633822886984823975214363968001,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord413 : orderSearch 6 6 324517318136239080314860436450806 [324517318136239080314860436450806,324517315718387453247965072892240,633825300114100176419220670051,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord414 : orderSearch 6 6 324517318136239080314860436450806 [324517318136239080314860436450806,2417851638347927698263526,324517315718387453247965072892240,633825300114100176419220670051,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord415 : orderSearch 6 6 323885966298342689179026460989868 [323885966298342689179026460989868,2417842429535473200466308,323885963880500264155966194405544,633825300114100176419220670051,633822886984823975214363968001,2417851638347927698263526,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord416 : orderSearch 6 6 324517318136229873758612405594580 [324517318136229873758612405594580,2417842429535473200466308,324517315718387453247965072892240,633825300114100176419220670051,633822886984823975214363968001,2417851638347927698263526,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord417 : orderSearch 6 6 323884728358312612082407668973568 [323884728358312612082407668973568,323885963880500264155966194405544,324517315718387453247965072892240,633825300114100176419220670051,633822886984823975214363968001,2417851638347927698263526,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord418 : orderSearch 6 6 324518551240575105321523598324216 [324518551240575105321523598324216,323885963880500264155966194405544,324517315718387453247965072892240,633825300114100176419220670051,633822886984823975214363968001,2417851638347927698263526,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord419 : orderSearch 7 7 633825300114100176419220670051 [633825300114100176419220670051,633822886984823975214363968001,2417851638347927698263526,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  apply ocover_step (states := [(6,2417851624669675992433762,[2417851624669675992433762,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240]),(6,2417851624669675992433762,[2417851624669675992433762,633825300114100176419220670051,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240]),(6,2417851624669675992433762,[2417851624669675992433762,2417851638347927698263526,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240]),(6,2417851624669675992433762,[2417851624669675992433762,633825300114100176419220670051,2417851638347927698263526,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240]),(6,633825300114113854670926499815,[633825300114113854670926499815,633825300114100176419220670051,2417851638347927698263526,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240]),(6,2417842415857221494636544,[2417842415857221494636544,633822886984823975214363968001,2417851638347927698263526,323885963880500264155966194405544,324517315718387453247965072892240]),(6,2417842415857221494636544,[2417842415857221494636544,633825300114100176419220670051,633822886984823975214363968001,2417851638347927698263526,323885963880500264155966194405544,324517315718387453247965072892240]),(6,2417842415857221494636544,[2417842415857221494636544,2417842429535473200466308,633822886984823975214363968001,2417851638347927698263526,323885963880500264155966194405544,324517315718387453247965072892240]),(6,2417842415857221494636544,[2417842415857221494636544,633825300114100176419220670051,2417842429535473200466308,633822886984823975214363968001,2417851638347927698263526,323885963880500264155966194405544,324517315718387453247965072892240]),(6,633825300114113854670926499815,[633825300114113854670926499815,633825300114100176419220670051,2417842429535473200466308,633822886984823975214363968001,2417851638347927698263526,323885963880500264155966194405544,324517315718387453247965072892240]),(6,1235522187647279119783182368,[1235522187647279119783182368,633825300114100176419220670051,323885963880500264155966194405544,633822886984823975214363968001,2417851638347927698263526,2417842429535473200466308,324517315718387453247965072892240]),(6,324518553658426717053265631893227,[324518553658426717053265631893227,633825300114100176419220670051,323885963880500264155966194405544,633822886984823975214363968001,2417851638347927698263526,2417842429535473200466308,324517315718387453247965072892240]),(6,632587360074831576679919419456,[632587360074831576679919419456,633825300114100176419220670051,324517315718387453247965072892240,633822886984823975214363968001,2417851638347927698263526,2417842429535473200466308,323885963880500264155966194405544]),(6,324518553658426721847704374142835,[324518553658426721847704374142835,633825300114100176419220670051,324517315718387453247965072892240,633822886984823975214363968001,2417851638347927698263526,2417842429535473200466308,323885963880500264155966194405544]),(6,633825300114113854670926499815,[633825300114113854670926499815,633822886984823975214363968001,2417851638347927698263526,633825300114100176419220670051,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240]),(6,633825300114110399854773996421,[633825300114110399854773996421,633825300114100176419220670051,2417851638347927698263526,323885963880500264155966194405544,324517315718387453247965072892240]),(6,633825300114110399854773996421,[633825300114110399854773996421,633822886984823975214363968001,633825300114100176419220670051,2417851638347927698263526,323885963880500264155966194405544,324517315718387453247965072892240]),(6,633825300114110399854773996421,[633825300114110399854773996421,2417842429535473200466308,633825300114100176419220670051,2417851638347927698263526,323885963880500264155966194405544,324517315718387453247965072892240]),(6,633825300114110399854773996421,[633825300114110399854773996421,633822886984823975214363968001,2417842429535473200466308,633825300114100176419220670051,2417851638347927698263526,323885963880500264155966194405544,324517315718387453247965072892240]),(6,324518551245297441980164008661673,[324518551245297441980164008661673,633822886984823975214363968001,323885963880500264155966194405544,633825300114100176419220670051,2417851638347927698263526,2417842429535473200466308,324517315718387453247965072892240]),(6,324518551245297447902705984381777,[324518551245297447902705984381777,633822886984823975214363968001,324517315718387453247965072892240,633825300114100176419220670051,2417851638347927698263526,2417842429535473200466308,323885963880500264155966194405544]),(6,323885966298351896863377725316590,[323885966298351896863377725316590,323885963880500264155966194405544,633825300114100176419220670051,633822886984823975214363968001,2417842429535473200466308,324517315718387453247965072892240]),(6,323885966298351896863377725316590,[323885966298351896863377725316590,2417851638347927698263526,323885963880500264155966194405544,633825300114100176419220670051,633822886984823975214363968001,2417842429535473200466308,324517315718387453247965072892240]),(6,324517318136239080314860436450806,[324517318136239080314860436450806,324517315718387453247965072892240,633825300114100176419220670051,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544]),(6,324517318136239080314860436450806,[324517318136239080314860436450806,2417851638347927698263526,324517315718387453247965072892240,633825300114100176419220670051,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544]),(6,323885966298342689179026460989868,[323885966298342689179026460989868,2417842429535473200466308,323885963880500264155966194405544,633825300114100176419220670051,633822886984823975214363968001,2417851638347927698263526,324517315718387453247965072892240]),(6,324517318136229873758612405594580,[324517318136229873758612405594580,2417842429535473200466308,324517315718387453247965072892240,633825300114100176419220670051,633822886984823975214363968001,2417851638347927698263526,323885963880500264155966194405544]),(6,323884728358312612082407668973568,[323884728358312612082407668973568,323885963880500264155966194405544,324517315718387453247965072892240,633825300114100176419220670051,633822886984823975214363968001,2417851638347927698263526,2417842429535473200466308]),(6,324518551240575105321523598324216,[324518551240575105321523598324216,323885963880500264155966194405544,324517315718387453247965072892240,633825300114100176419220670051,633822886984823975214363968001,2417851638347927698263526,2417842429535473200466308])])
  · decide +kernel
  · simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.not_false, ord390, ord391, ord392, ord393, ord394, ord395, ord396, ord397, ord398, ord399, ord400, ord401, ord402, ord403, ord404, ord405, ord406, ord407, ord408, ord409, ord410, ord411, ord412, ord413, ord414, ord415, ord416, ord417, ord418]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord420 : orderSearch 7 7 633825300114100176419220670051 [633825300114100176419220670051,2413138481558843201995874,633822886984823975214363968001,2417851638347927698263526,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord421 : orderSearch 7 7 323885966293638744586706162930922 [323885966293638744586706162930922,2413138481558843201995874,323885963880500264155966194405544,2417851638347927698263526,2417842429535473200466308,633822886984823975214363968001,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord422 : orderSearch 7 7 324517318131525932550601807947122 [324517318131525932550601807947122,2413138481558843201995874,324517315718387453247965072892240,2417851638347927698263526,2417842429535473200466308,633822886984823975214363968001,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord423 : orderSearch 7 7 633825300114110399854773996421 [633825300114110399854773996421,633822886984823975214363968001,2417851638347927698263526,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord424 : orderSearch 7 7 633825300114110399854773996421 [633825300114110399854773996421,2417842429535473200466308,633822886984823975214363968001,2417851638347927698263526,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord425 : orderSearch 7 7 323885966298342689179026460989868 [323885966298342689179026460989868,2417842429535473200466308,323885963880500264155966194405544,2417851638347927698263526,2413138481558843201995874,633822886984823975214363968001,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord426 : orderSearch 7 7 324517318136229873758612405594580 [324517318136229873758612405594580,2417842429535473200466308,324517315718387453247965072892240,2417851638347927698263526,2413138481558843201995874,633822886984823975214363968001,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord427 : orderSearch 7 7 1235522187646151016549711872 [1235522187646151016549711872,633822886984823975214363968001,323885963880500264155966194405544,2417851638347927698263526,2413138481558843201995874,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord428 : orderSearch 7 7 324518551245297441980164008661673 [324518551245297441980164008661673,633822886984823975214363968001,323885963880500264155966194405544,2417851638347927698263526,2413138481558843201995874,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord429 : orderSearch 7 7 632587360074829320473452478464 [632587360074829320473452478464,633822886984823975214363968001,324517315718387453247965072892240,2417851638347927698263526,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord430 : orderSearch 7 7 324518551245297447902705984381777 [324518551245297447902705984381777,633822886984823975214363968001,324517315718387453247965072892240,2417851638347927698263526,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord431 : orderSearch 7 7 323884728358312612082407668973568 [323884728358312612082407668973568,323885963880500264155966194405544,324517315718387453247965072892240,2417851638347927698263526,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord432 : orderSearch 7 7 324518551240575105321523598324216 [324518551240575105321523598324216,323885963880500264155966194405544,324517315718387453247965072892240,2417851638347927698263526,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord433 : orderSearch 8 8 2417851638347927698263526 [2417851638347927698263526,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  apply ocover_step (states := [(7,4722348468471135731712,[4722348468471135731712,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240]),(7,4722348468471135731712,[4722348468471135731712,2417851638347927698263526,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240]),(7,633825300114113854670926499815,[633825300114113854670926499815,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240]),(7,633825300114113854670926499815,[633825300114113854670926499815,2417851638347927698263526,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240]),(7,5640516167352480,[5640516167352480,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001,324517315718387453247965072892240]),(7,5640516167352480,[5640516167352480,2417851638347927698263526,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001,324517315718387453247965072892240]),(7,323885966298351896863377725316590,[323885966298351896863377725316590,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001,324517315718387453247965072892240]),(7,323885966298351896863377725316590,[323885966298351896863377725316590,2417851638347927698263526,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001,324517315718387453247965072892240]),(7,11281032334704960,[11281032334704960,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001,323885963880500264155966194405544]),(7,11281032334704960,[11281032334704960,2417851638347927698263526,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001,323885963880500264155966194405544]),(7,324517318136239080314860436450806,[324517318136239080314860436450806,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001,323885963880500264155966194405544]),(7,324517318136239080314860436450806,[324517318136239080314860436450806,2417851638347927698263526,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001,323885963880500264155966194405544]),(7,633825300114100176419220670051,[633825300114100176419220670051,633822886984823975214363968001,2417851638347927698263526,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240]),(7,633825300114100176419220670051,[633825300114100176419220670051,2413138481558843201995874,633822886984823975214363968001,2417851638347927698263526,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240]),(7,323885966293638744586706162930922,[323885966293638744586706162930922,2413138481558843201995874,323885963880500264155966194405544,2417851638347927698263526,2417842429535473200466308,633822886984823975214363968001,324517315718387453247965072892240]),(7,324517318131525932550601807947122,[324517318131525932550601807947122,2413138481558843201995874,324517315718387453247965072892240,2417851638347927698263526,2417842429535473200466308,633822886984823975214363968001,323885963880500264155966194405544]),(7,633825300114110399854773996421,[633825300114110399854773996421,633822886984823975214363968001,2417851638347927698263526,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240]),(7,633825300114110399854773996421,[633825300114110399854773996421,2417842429535473200466308,633822886984823975214363968001,2417851638347927698263526,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240]),(7,323885966298342689179026460989868,[323885966298342689179026460989868,2417842429535473200466308,323885963880500264155966194405544,2417851638347927698263526,2413138481558843201995874,633822886984823975214363968001,324517315718387453247965072892240]),(7,324517318136229873758612405594580,[324517318136229873758612405594580,2417842429535473200466308,324517315718387453247965072892240,2417851638347927698263526,2413138481558843201995874,633822886984823975214363968001,323885963880500264155966194405544]),(7,1235522187646151016549711872,[1235522187646151016549711872,633822886984823975214363968001,323885963880500264155966194405544,2417851638347927698263526,2413138481558843201995874,2417842429535473200466308,324517315718387453247965072892240]),(7,324518551245297441980164008661673,[324518551245297441980164008661673,633822886984823975214363968001,323885963880500264155966194405544,2417851638347927698263526,2413138481558843201995874,2417842429535473200466308,324517315718387453247965072892240]),(7,632587360074829320473452478464,[632587360074829320473452478464,633822886984823975214363968001,324517315718387453247965072892240,2417851638347927698263526,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544]),(7,324518551245297447902705984381777,[324518551245297447902705984381777,633822886984823975214363968001,324517315718387453247965072892240,2417851638347927698263526,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544]),(7,323884728358312612082407668973568,[323884728358312612082407668973568,323885963880500264155966194405544,324517315718387453247965072892240,2417851638347927698263526,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001]),(7,324518551240575105321523598324216,[324518551240575105321523598324216,323885963880500264155966194405544,324517315718387453247965072892240,2417851638347927698263526,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001])])
  · decide +kernel
  · simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.not_false, ord378, ord379, ord380, ord381, ord382, ord383, ord384, ord385, ord386, ord387, ord388, ord389, ord419, ord420, ord421, ord422, ord423, ord424, ord425, ord426, ord427, ord428, ord429, ord430, ord431, ord432]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord434 : orderSearch 7 7 0 [0,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord435 : orderSearch 7 7 0 [0,1128103233470496,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord436 : orderSearch 7 6 633822886984825103317597438497 [633822886984825103317597438497,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord437 : orderSearch 7 6 633822886984825103317597438497 [633822886984825103317597438497,1128103233470496,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord438 : orderSearch 7 7 0 [0,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544,633822886984823975214363968001,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord439 : orderSearch 7 7 0 [0,1128103233470496,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544,633822886984823975214363968001,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord440 : orderSearch 7 6 2417842430663576433936804 [2417842430663576433936804,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544,633822886984823975214363968001,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord441 : orderSearch 7 6 2417842430663576433936804 [2417842430663576433936804,1128103233470496,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544,633822886984823975214363968001,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord442 : orderSearch 7 7 0 [0,324517315718387453247965072892240,2413138481558843201995874,323885963880500264155966194405544,633822886984823975214363968001,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord443 : orderSearch 7 7 0 [0,1128103233470496,324517315718387453247965072892240,2413138481558843201995874,323885963880500264155966194405544,633822886984823975214363968001,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord444 : orderSearch 7 6 324517315718387454376068306362736 [324517315718387454376068306362736,324517315718387453247965072892240,2413138481558843201995874,323885963880500264155966194405544,633822886984823975214363968001,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord445 : orderSearch 7 6 324517315718387454376068306362736 [324517315718387454376068306362736,1128103233470496,324517315718387453247965072892240,2413138481558843201995874,323885963880500264155966194405544,633822886984823975214363968001,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord446 : orderSearch 7 7 323885966293638744586706162930922 [323885966293638744586706162930922,2413138481558843201995874,323885963880500264155966194405544,1128103233470496,633822886984823975214363968001,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord447 : orderSearch 7 7 9205357638345293824 [9205357638345293824,2413138481558843201995874,633822886984823975214363968001,1128103233470496,323885963880500264155966194405544,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord448 : orderSearch 7 7 633825300114100176419220670051 [633825300114100176419220670051,2413138481558843201995874,633822886984823975214363968001,1128103233470496,323885963880500264155966194405544,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord449 : orderSearch 7 7 2413129272746388704198656 [2413129272746388704198656,2413138481558843201995874,2417842429535473200466308,1128103233470496,323885963880500264155966194405544,633822886984823975214363968001,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord450 : orderSearch 7 7 2417851638347927698263526 [2417851638347927698263526,2413138481558843201995874,2417842429535473200466308,1128103233470496,323885963880500264155966194405544,633822886984823975214363968001,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord451 : orderSearch 7 7 2256206466940992 [2256206466940992,2413138481558843201995874,324517315718387453247965072892240,1128103233470496,323885963880500264155966194405544,633822886984823975214363968001,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord452 : orderSearch 7 7 324517318131525932550601807947122 [324517318131525932550601807947122,2413138481558843201995874,324517315718387453247965072892240,1128103233470496,323885963880500264155966194405544,633822886984823975214363968001,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord453 : orderSearch 7 7 1235522187646151016549711872 [1235522187646151016549711872,323885963880500264155966194405544,633822886984823975214363968001,1128103233470496,2413138481558843201995874,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord454 : orderSearch 7 7 324518551245297441980164008661673 [324518551245297441980164008661673,323885963880500264155966194405544,633822886984823975214363968001,1128103233470496,2413138481558843201995874,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord455 : orderSearch 7 7 4512412933881984 [4512412933881984,323885963880500264155966194405544,2417842429535473200466308,1128103233470496,2413138481558843201995874,633822886984823975214363968001,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord456 : orderSearch 7 7 323885966298342689179026460989868 [323885966298342689179026460989868,323885963880500264155966194405544,2417842429535473200466308,1128103233470496,2413138481558843201995874,633822886984823975214363968001,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord457 : orderSearch 7 7 323884728358312612082407668973568 [323884728358312612082407668973568,323885963880500264155966194405544,324517315718387453247965072892240,1128103233470496,2413138481558843201995874,633822886984823975214363968001,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord458 : orderSearch 7 7 324518551240575105321523598324216 [324518551240575105321523598324216,323885963880500264155966194405544,324517315718387453247965072892240,1128103233470496,2413138481558843201995874,633822886984823975214363968001,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord459 : orderSearch 7 7 4713143110832790437888 [4713143110832790437888,633822886984823975214363968001,2417842429535473200466308,1128103233470496,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord460 : orderSearch 7 7 633825300114110399854773996421 [633825300114110399854773996421,633822886984823975214363968001,2417842429535473200466308,1128103233470496,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord461 : orderSearch 7 7 632587360074829320473452478464 [632587360074829320473452478464,633822886984823975214363968001,324517315718387453247965072892240,1128103233470496,2413138481558843201995874,323885963880500264155966194405544,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord462 : orderSearch 7 7 324518551245297447902705984381777 [324518551245297447902705984381777,633822886984823975214363968001,324517315718387453247965072892240,1128103233470496,2413138481558843201995874,323885963880500264155966194405544,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord463 : orderSearch 7 7 9024825867763968 [9024825867763968,2417842429535473200466308,324517315718387453247965072892240,1128103233470496,2413138481558843201995874,323885963880500264155966194405544,633822886984823975214363968001] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord464 : orderSearch 7 7 324517318136229873758612405594580 [324517318136229873758612405594580,2417842429535473200466308,324517315718387453247965072892240,1128103233470496,2413138481558843201995874,323885963880500264155966194405544,633822886984823975214363968001] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord465 : orderSearch 8 8 1128103233470496 [1128103233470496,2413138481558843201995874,323885963880500264155966194405544,633822886984823975214363968001,2417842429535473200466308,324517315718387453247965072892240] = false := by
  apply ocover_step (states := [(7,0,[0,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544,2417842429535473200466308,324517315718387453247965072892240]),(7,0,[0,1128103233470496,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544,2417842429535473200466308,324517315718387453247965072892240]),(6,633822886984825103317597438497,[633822886984825103317597438497,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544,2417842429535473200466308,324517315718387453247965072892240]),(6,633822886984825103317597438497,[633822886984825103317597438497,1128103233470496,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544,2417842429535473200466308,324517315718387453247965072892240]),(7,0,[0,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544,633822886984823975214363968001,324517315718387453247965072892240]),(7,0,[0,1128103233470496,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544,633822886984823975214363968001,324517315718387453247965072892240]),(6,2417842430663576433936804,[2417842430663576433936804,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544,633822886984823975214363968001,324517315718387453247965072892240]),(6,2417842430663576433936804,[2417842430663576433936804,1128103233470496,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544,633822886984823975214363968001,324517315718387453247965072892240]),(7,0,[0,324517315718387453247965072892240,2413138481558843201995874,323885963880500264155966194405544,633822886984823975214363968001,2417842429535473200466308]),(7,0,[0,1128103233470496,324517315718387453247965072892240,2413138481558843201995874,323885963880500264155966194405544,633822886984823975214363968001,2417842429535473200466308]),(6,324517315718387454376068306362736,[324517315718387454376068306362736,324517315718387453247965072892240,2413138481558843201995874,323885963880500264155966194405544,633822886984823975214363968001,2417842429535473200466308]),(6,324517315718387454376068306362736,[324517315718387454376068306362736,1128103233470496,324517315718387453247965072892240,2413138481558843201995874,323885963880500264155966194405544,633822886984823975214363968001,2417842429535473200466308]),(7,323885966293638744586706162930922,[323885966293638744586706162930922,2413138481558843201995874,323885963880500264155966194405544,1128103233470496,633822886984823975214363968001,2417842429535473200466308,324517315718387453247965072892240]),(7,9205357638345293824,[9205357638345293824,2413138481558843201995874,633822886984823975214363968001,1128103233470496,323885963880500264155966194405544,2417842429535473200466308,324517315718387453247965072892240]),(7,633825300114100176419220670051,[633825300114100176419220670051,2413138481558843201995874,633822886984823975214363968001,1128103233470496,323885963880500264155966194405544,2417842429535473200466308,324517315718387453247965072892240]),(7,2413129272746388704198656,[2413129272746388704198656,2413138481558843201995874,2417842429535473200466308,1128103233470496,323885963880500264155966194405544,633822886984823975214363968001,324517315718387453247965072892240]),(7,2417851638347927698263526,[2417851638347927698263526,2413138481558843201995874,2417842429535473200466308,1128103233470496,323885963880500264155966194405544,633822886984823975214363968001,324517315718387453247965072892240]),(7,2256206466940992,[2256206466940992,2413138481558843201995874,324517315718387453247965072892240,1128103233470496,323885963880500264155966194405544,633822886984823975214363968001,2417842429535473200466308]),(7,324517318131525932550601807947122,[324517318131525932550601807947122,2413138481558843201995874,324517315718387453247965072892240,1128103233470496,323885963880500264155966194405544,633822886984823975214363968001,2417842429535473200466308]),(7,1235522187646151016549711872,[1235522187646151016549711872,323885963880500264155966194405544,633822886984823975214363968001,1128103233470496,2413138481558843201995874,2417842429535473200466308,324517315718387453247965072892240]),(7,324518551245297441980164008661673,[324518551245297441980164008661673,323885963880500264155966194405544,633822886984823975214363968001,1128103233470496,2413138481558843201995874,2417842429535473200466308,324517315718387453247965072892240]),(7,4512412933881984,[4512412933881984,323885963880500264155966194405544,2417842429535473200466308,1128103233470496,2413138481558843201995874,633822886984823975214363968001,324517315718387453247965072892240]),(7,323885966298342689179026460989868,[323885966298342689179026460989868,323885963880500264155966194405544,2417842429535473200466308,1128103233470496,2413138481558843201995874,633822886984823975214363968001,324517315718387453247965072892240]),(7,323884728358312612082407668973568,[323884728358312612082407668973568,323885963880500264155966194405544,324517315718387453247965072892240,1128103233470496,2413138481558843201995874,633822886984823975214363968001,2417842429535473200466308]),(7,324518551240575105321523598324216,[324518551240575105321523598324216,323885963880500264155966194405544,324517315718387453247965072892240,1128103233470496,2413138481558843201995874,633822886984823975214363968001,2417842429535473200466308]),(7,4713143110832790437888,[4713143110832790437888,633822886984823975214363968001,2417842429535473200466308,1128103233470496,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240]),(7,633825300114110399854773996421,[633825300114110399854773996421,633822886984823975214363968001,2417842429535473200466308,1128103233470496,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240]),(7,632587360074829320473452478464,[632587360074829320473452478464,633822886984823975214363968001,324517315718387453247965072892240,1128103233470496,2413138481558843201995874,323885963880500264155966194405544,2417842429535473200466308]),(7,324518551245297447902705984381777,[324518551245297447902705984381777,633822886984823975214363968001,324517315718387453247965072892240,1128103233470496,2413138481558843201995874,323885963880500264155966194405544,2417842429535473200466308]),(7,9024825867763968,[9024825867763968,2417842429535473200466308,324517315718387453247965072892240,1128103233470496,2413138481558843201995874,323885963880500264155966194405544,633822886984823975214363968001]),(7,324517318136229873758612405594580,[324517318136229873758612405594580,2417842429535473200466308,324517315718387453247965072892240,1128103233470496,2413138481558843201995874,323885963880500264155966194405544,633822886984823975214363968001])])
  · decide +kernel
  · simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.not_false, ord434, ord435, ord436, ord437, ord438, ord439, ord440, ord441, ord442, ord443, ord444, ord445, ord446, ord447, ord448, ord449, ord450, ord451, ord452, ord453, ord454, ord455, ord456, ord457, ord458, ord459, ord460, ord461, ord462, ord463, ord464]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord466 : orderSearch 7 7 1235522196851508654895005696 [1235522196851508654895005696,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord467 : orderSearch 7 7 1235522196851508654895005696 [1235522196851508654895005696,323885966293638744586706162930922,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord468 : orderSearch 7 7 324518553658426717053265631893227 [324518553658426717053265631893227,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord469 : orderSearch 7 7 324518553658426717053265631893227 [324518553658426717053265631893227,323885966293638744586706162930922,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord470 : orderSearch 7 7 2413129277258801638080640 [2413129277258801638080640,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544,633822886984823975214363968001,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord471 : orderSearch 7 7 2413129277258801638080640 [2413129277258801638080640,323885966293638744586706162930922,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544,633822886984823975214363968001,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord472 : orderSearch 7 7 323885966298351896863377725316590 [323885966298351896863377725316590,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544,633822886984823975214363968001,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord473 : orderSearch 7 7 323885966298351896863377725316590 [323885966298351896863377725316590,323885966293638744586706162930922,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544,633822886984823975214363968001,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord474 : orderSearch 7 7 323884728358312614338614135914560 [323884728358312614338614135914560,324517315718387453247965072892240,2413138481558843201995874,323885963880500264155966194405544,633822886984823975214363968001,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord475 : orderSearch 7 7 323884728358312614338614135914560 [323884728358312614338614135914560,323885966293638744586706162930922,324517315718387453247965072892240,2413138481558843201995874,323885963880500264155966194405544,633822886984823975214363968001,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord476 : orderSearch 7 7 324518553653713583496057099908602 [324518553653713583496057099908602,324517315718387453247965072892240,2413138481558843201995874,323885963880500264155966194405544,633822886984823975214363968001,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord477 : orderSearch 7 7 324518553653713583496057099908602 [324518553653713583496057099908602,323885966293638744586706162930922,324517315718387453247965072892240,2413138481558843201995874,323885963880500264155966194405544,633822886984823975214363968001,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord478 : orderSearch 7 7 324517318131525932550601807947122 [324517318131525932550601807947122,324517315718387453247965072892240,323885966293638744586706162930922,323885963880500264155966194405544,633822886984823975214363968001,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord479 : orderSearch 7 7 324517318131525932550601807947122 [324517318131525932550601807947122,2413138481558843201995874,324517315718387453247965072892240,323885966293638744586706162930922,323885963880500264155966194405544,633822886984823975214363968001,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord480 : orderSearch 7 7 324518551245297441980164008661673 [324518551245297441980164008661673,633822886984823975214363968001,323885966293638744586706162930922,2413138481558843201995874,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord481 : orderSearch 7 7 324518551245297441980164008661673 [324518551245297441980164008661673,323885963880500264155966194405544,633822886984823975214363968001,323885966293638744586706162930922,2413138481558843201995874,2417842429535473200466308,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord482 : orderSearch 7 7 323885966298342689179026460989868 [323885966298342689179026460989868,2417842429535473200466308,323885966293638744586706162930922,2413138481558843201995874,633822886984823975214363968001,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord483 : orderSearch 7 7 323885966298342689179026460989868 [323885966298342689179026460989868,323885963880500264155966194405544,2417842429535473200466308,323885966293638744586706162930922,2413138481558843201995874,633822886984823975214363968001,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord484 : orderSearch 7 7 324518551240575105321523598324216 [324518551240575105321523598324216,323885963880500264155966194405544,324517315718387453247965072892240,323885966293638744586706162930922,2413138481558843201995874,633822886984823975214363968001,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord485 : orderSearch 7 7 324518551245297447902705984381777 [324518551245297447902705984381777,633822886984823975214363968001,324517315718387453247965072892240,323885966293638744586706162930922,2413138481558843201995874,323885963880500264155966194405544,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord486 : orderSearch 7 7 324517318136229873758612405594580 [324517318136229873758612405594580,2417842429535473200466308,324517315718387453247965072892240,323885966293638744586706162930922,2413138481558843201995874,323885963880500264155966194405544,633822886984823975214363968001] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord487 : orderSearch 8 8 323885966293638744586706162930922 [323885966293638744586706162930922,2413138481558843201995874,323885963880500264155966194405544,633822886984823975214363968001,2417842429535473200466308,324517315718387453247965072892240] = false := by
  apply ocover_step (states := [(7,1235522196851508654895005696,[1235522196851508654895005696,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544,2417842429535473200466308,324517315718387453247965072892240]),(7,1235522196851508654895005696,[1235522196851508654895005696,323885966293638744586706162930922,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544,2417842429535473200466308,324517315718387453247965072892240]),(7,324518553658426717053265631893227,[324518553658426717053265631893227,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544,2417842429535473200466308,324517315718387453247965072892240]),(7,324518553658426717053265631893227,[324518553658426717053265631893227,323885966293638744586706162930922,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544,2417842429535473200466308,324517315718387453247965072892240]),(7,2413129277258801638080640,[2413129277258801638080640,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544,633822886984823975214363968001,324517315718387453247965072892240]),(7,2413129277258801638080640,[2413129277258801638080640,323885966293638744586706162930922,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544,633822886984823975214363968001,324517315718387453247965072892240]),(7,323885966298351896863377725316590,[323885966298351896863377725316590,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544,633822886984823975214363968001,324517315718387453247965072892240]),(7,323885966298351896863377725316590,[323885966298351896863377725316590,323885966293638744586706162930922,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544,633822886984823975214363968001,324517315718387453247965072892240]),(7,323884728358312614338614135914560,[323884728358312614338614135914560,324517315718387453247965072892240,2413138481558843201995874,323885963880500264155966194405544,633822886984823975214363968001,2417842429535473200466308]),(7,323884728358312614338614135914560,[323884728358312614338614135914560,323885966293638744586706162930922,324517315718387453247965072892240,2413138481558843201995874,323885963880500264155966194405544,633822886984823975214363968001,2417842429535473200466308]),(7,324518553653713583496057099908602,[324518553653713583496057099908602,324517315718387453247965072892240,2413138481558843201995874,323885963880500264155966194405544,633822886984823975214363968001,2417842429535473200466308]),(7,324518553653713583496057099908602,[324518553653713583496057099908602,323885966293638744586706162930922,324517315718387453247965072892240,2413138481558843201995874,323885963880500264155966194405544,633822886984823975214363968001,2417842429535473200466308]),(7,324517318131525932550601807947122,[324517318131525932550601807947122,324517315718387453247965072892240,323885966293638744586706162930922,323885963880500264155966194405544,633822886984823975214363968001,2417842429535473200466308]),(7,324517318131525932550601807947122,[324517318131525932550601807947122,2413138481558843201995874,324517315718387453247965072892240,323885966293638744586706162930922,323885963880500264155966194405544,633822886984823975214363968001,2417842429535473200466308]),(7,324518551245297441980164008661673,[324518551245297441980164008661673,633822886984823975214363968001,323885966293638744586706162930922,2413138481558843201995874,2417842429535473200466308,324517315718387453247965072892240]),(7,324518551245297441980164008661673,[324518551245297441980164008661673,323885963880500264155966194405544,633822886984823975214363968001,323885966293638744586706162930922,2413138481558843201995874,2417842429535473200466308,324517315718387453247965072892240]),(7,323885966298342689179026460989868,[323885966298342689179026460989868,2417842429535473200466308,323885966293638744586706162930922,2413138481558843201995874,633822886984823975214363968001,324517315718387453247965072892240]),(7,323885966298342689179026460989868,[323885966298342689179026460989868,323885963880500264155966194405544,2417842429535473200466308,323885966293638744586706162930922,2413138481558843201995874,633822886984823975214363968001,324517315718387453247965072892240]),(7,324518551240575105321523598324216,[324518551240575105321523598324216,323885963880500264155966194405544,324517315718387453247965072892240,323885966293638744586706162930922,2413138481558843201995874,633822886984823975214363968001,2417842429535473200466308]),(7,324518551245297447902705984381777,[324518551245297447902705984381777,633822886984823975214363968001,324517315718387453247965072892240,323885966293638744586706162930922,2413138481558843201995874,323885963880500264155966194405544,2417842429535473200466308]),(7,324517318136229873758612405594580,[324517318136229873758612405594580,2417842429535473200466308,324517315718387453247965072892240,323885966293638744586706162930922,2413138481558843201995874,323885963880500264155966194405544,633822886984823975214363968001])])
  · decide +kernel
  · simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.not_false, ord466, ord467, ord468, ord469, ord470, ord471, ord472, ord473, ord474, ord475, ord476, ord477, ord478, ord479, ord480, ord481, ord482, ord483, ord484, ord485, ord486]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord488 : orderSearch 8 8 2256206466940992 [2256206466940992,2413138481558843201995874,324517315718387453247965072892240,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord489 : orderSearch 7 7 632587360084034678111797772288 [632587360084034678111797772288,633822886984823975214363968001,2413138481558843201995874,324517315718387453247965072892240,2417842429535473200466308,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord490 : orderSearch 7 7 632587360084034678111797772288 [632587360084034678111797772288,324517318131525932550601807947122,633822886984823975214363968001,2413138481558843201995874,324517315718387453247965072892240,2417842429535473200466308,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord491 : orderSearch 7 7 324518553658426721847704374142835 [324518553658426721847704374142835,633822886984823975214363968001,2413138481558843201995874,324517315718387453247965072892240,2417842429535473200466308,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord492 : orderSearch 7 7 324518553658426721847704374142835 [324518553658426721847704374142835,324517318131525932550601807947122,633822886984823975214363968001,2413138481558843201995874,324517315718387453247965072892240,2417842429535473200466308,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord493 : orderSearch 7 7 2413129281771214571962624 [2413129281771214571962624,2417842429535473200466308,2413138481558843201995874,324517315718387453247965072892240,633822886984823975214363968001,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord494 : orderSearch 7 7 2413129281771214571962624 [2413129281771214571962624,324517318131525932550601807947122,2417842429535473200466308,2413138481558843201995874,324517315718387453247965072892240,633822886984823975214363968001,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord495 : orderSearch 7 7 324517318136239080314860436450806 [324517318136239080314860436450806,2417842429535473200466308,2413138481558843201995874,324517315718387453247965072892240,633822886984823975214363968001,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord496 : orderSearch 7 7 324517318136239080314860436450806 [324517318136239080314860436450806,324517318131525932550601807947122,2417842429535473200466308,2413138481558843201995874,324517315718387453247965072892240,633822886984823975214363968001,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord497 : orderSearch 7 7 323884728358312613210510902444064 [323884728358312613210510902444064,323885963880500264155966194405544,2413138481558843201995874,324517315718387453247965072892240,633822886984823975214363968001,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord498 : orderSearch 7 7 323884728358312613210510902444064 [323884728358312613210510902444064,324517318131525932550601807947122,323885963880500264155966194405544,2413138481558843201995874,324517315718387453247965072892240,633822886984823975214363968001,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord499 : orderSearch 7 7 324518553653713583496057099908602 [324518553653713583496057099908602,323885963880500264155966194405544,2413138481558843201995874,324517315718387453247965072892240,633822886984823975214363968001,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord500 : orderSearch 7 7 324518553653713583496057099908602 [324518553653713583496057099908602,324517318131525932550601807947122,323885963880500264155966194405544,2413138481558843201995874,324517315718387453247965072892240,633822886984823975214363968001,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord501 : orderSearch 7 7 324518551245297447902705984381777 [324518551245297447902705984381777,633822886984823975214363968001,324517318131525932550601807947122,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord502 : orderSearch 7 7 324518551245297447902705984381777 [324518551245297447902705984381777,324517315718387453247965072892240,633822886984823975214363968001,324517318131525932550601807947122,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord503 : orderSearch 7 7 324517318136229873758612405594580 [324517318136229873758612405594580,2417842429535473200466308,324517318131525932550601807947122,2413138481558843201995874,633822886984823975214363968001,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord504 : orderSearch 7 7 324517318136229873758612405594580 [324517318136229873758612405594580,324517315718387453247965072892240,2417842429535473200466308,324517318131525932550601807947122,2413138481558843201995874,633822886984823975214363968001,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord505 : orderSearch 7 7 324518551240575105321523598324216 [324518551240575105321523598324216,324517315718387453247965072892240,323885963880500264155966194405544,324517318131525932550601807947122,2413138481558843201995874,633822886984823975214363968001,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord506 : orderSearch 7 7 324518551245297441980164008661673 [324518551245297441980164008661673,633822886984823975214363968001,323885963880500264155966194405544,324517318131525932550601807947122,2413138481558843201995874,324517315718387453247965072892240,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord507 : orderSearch 8 8 324517318131525932550601807947122 [324517318131525932550601807947122,2413138481558843201995874,324517315718387453247965072892240,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544] = false := by
  apply ocover_step (states := [(7,632587360084034678111797772288,[632587360084034678111797772288,633822886984823975214363968001,2413138481558843201995874,324517315718387453247965072892240,2417842429535473200466308,323885963880500264155966194405544]),(7,632587360084034678111797772288,[632587360084034678111797772288,324517318131525932550601807947122,633822886984823975214363968001,2413138481558843201995874,324517315718387453247965072892240,2417842429535473200466308,323885963880500264155966194405544]),(7,324518553658426721847704374142835,[324518553658426721847704374142835,633822886984823975214363968001,2413138481558843201995874,324517315718387453247965072892240,2417842429535473200466308,323885963880500264155966194405544]),(7,324518553658426721847704374142835,[324518553658426721847704374142835,324517318131525932550601807947122,633822886984823975214363968001,2413138481558843201995874,324517315718387453247965072892240,2417842429535473200466308,323885963880500264155966194405544]),(7,2413129281771214571962624,[2413129281771214571962624,2417842429535473200466308,2413138481558843201995874,324517315718387453247965072892240,633822886984823975214363968001,323885963880500264155966194405544]),(7,2413129281771214571962624,[2413129281771214571962624,324517318131525932550601807947122,2417842429535473200466308,2413138481558843201995874,324517315718387453247965072892240,633822886984823975214363968001,323885963880500264155966194405544]),(7,324517318136239080314860436450806,[324517318136239080314860436450806,2417842429535473200466308,2413138481558843201995874,324517315718387453247965072892240,633822886984823975214363968001,323885963880500264155966194405544]),(7,324517318136239080314860436450806,[324517318136239080314860436450806,324517318131525932550601807947122,2417842429535473200466308,2413138481558843201995874,324517315718387453247965072892240,633822886984823975214363968001,323885963880500264155966194405544]),(7,323884728358312613210510902444064,[323884728358312613210510902444064,323885963880500264155966194405544,2413138481558843201995874,324517315718387453247965072892240,633822886984823975214363968001,2417842429535473200466308]),(7,323884728358312613210510902444064,[323884728358312613210510902444064,324517318131525932550601807947122,323885963880500264155966194405544,2413138481558843201995874,324517315718387453247965072892240,633822886984823975214363968001,2417842429535473200466308]),(7,324518553653713583496057099908602,[324518553653713583496057099908602,323885963880500264155966194405544,2413138481558843201995874,324517315718387453247965072892240,633822886984823975214363968001,2417842429535473200466308]),(7,324518553653713583496057099908602,[324518553653713583496057099908602,324517318131525932550601807947122,323885963880500264155966194405544,2413138481558843201995874,324517315718387453247965072892240,633822886984823975214363968001,2417842429535473200466308]),(7,324518551245297447902705984381777,[324518551245297447902705984381777,633822886984823975214363968001,324517318131525932550601807947122,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544]),(7,324518551245297447902705984381777,[324518551245297447902705984381777,324517315718387453247965072892240,633822886984823975214363968001,324517318131525932550601807947122,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544]),(7,324517318136229873758612405594580,[324517318136229873758612405594580,2417842429535473200466308,324517318131525932550601807947122,2413138481558843201995874,633822886984823975214363968001,323885963880500264155966194405544]),(7,324517318136229873758612405594580,[324517318136229873758612405594580,324517315718387453247965072892240,2417842429535473200466308,324517318131525932550601807947122,2413138481558843201995874,633822886984823975214363968001,323885963880500264155966194405544]),(7,324518551240575105321523598324216,[324518551240575105321523598324216,324517315718387453247965072892240,323885963880500264155966194405544,324517318131525932550601807947122,2413138481558843201995874,633822886984823975214363968001,2417842429535473200466308]),(7,324518551245297441980164008661673,[324518551245297441980164008661673,633822886984823975214363968001,323885963880500264155966194405544,324517318131525932550601807947122,2413138481558843201995874,324517315718387453247965072892240,2417842429535473200466308])])
  · decide +kernel
  · simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.not_false, ord489, ord490, ord491, ord492, ord493, ord494, ord495, ord496, ord497, ord498, ord499, ord500, ord501, ord502, ord503, ord504, ord505, ord506]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord508 : orderSearch 8 8 4512412933881984 [4512412933881984,2417842429535473200466308,323885963880500264155966194405544,633822886984823975214363968001,2413138481558843201995874,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord509 : orderSearch 7 7 1235526900789261849340149760 [1235526900789261849340149760,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544,2413138481558843201995874,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord510 : orderSearch 7 7 1235526900789261849340149760 [1235526900789261849340149760,323885966298342689179026460989868,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544,2413138481558843201995874,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord511 : orderSearch 7 7 324518553658426723892391484808109 [324518553658426723892391484808109,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544,2413138481558843201995874,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord512 : orderSearch 7 7 324518553658426723892391484808109 [324518553658426723892391484808109,323885966298342689179026460989868,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544,2413138481558843201995874,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord513 : orderSearch 7 7 2413129273874491937669152 [2413129273874491937669152,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544,633822886984823975214363968001,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord514 : orderSearch 7 7 2413129273874491937669152 [2413129273874491937669152,323885966298342689179026460989868,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544,633822886984823975214363968001,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord515 : orderSearch 7 7 323885966298351896863377725316590 [323885966298351896863377725316590,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544,633822886984823975214363968001,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord516 : orderSearch 7 7 323885966298351896863377725316590 [323885966298351896863377725316590,323885966298342689179026460989868,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544,633822886984823975214363968001,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord517 : orderSearch 7 7 323884728358312621107233536737536 [323884728358312621107233536737536,324517315718387453247965072892240,2417842429535473200466308,323885963880500264155966194405544,633822886984823975214363968001,2413138481558843201995874] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord518 : orderSearch 7 7 323884728358312621107233536737536 [323884728358312621107233536737536,323885966298342689179026460989868,324517315718387453247965072892240,2417842429535473200466308,323885963880500264155966194405544,633822886984823975214363968001,2413138481558843201995874] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord519 : orderSearch 7 7 324518553658417521319757997144572 [324518553658417521319757997144572,324517315718387453247965072892240,2417842429535473200466308,323885963880500264155966194405544,633822886984823975214363968001,2413138481558843201995874] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord520 : orderSearch 7 7 324518553658417521319757997144572 [324518553658417521319757997144572,323885966298342689179026460989868,324517315718387453247965072892240,2417842429535473200466308,323885963880500264155966194405544,633822886984823975214363968001,2413138481558843201995874] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord521 : orderSearch 7 7 324517318136229873758612405594580 [324517318136229873758612405594580,324517315718387453247965072892240,323885966298342689179026460989868,323885963880500264155966194405544,633822886984823975214363968001,2413138481558843201995874] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord522 : orderSearch 7 7 324517318136229873758612405594580 [324517318136229873758612405594580,2417842429535473200466308,324517315718387453247965072892240,323885966298342689179026460989868,323885963880500264155966194405544,633822886984823975214363968001,2413138481558843201995874] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord523 : orderSearch 7 7 324518551245297441980164008661673 [324518551245297441980164008661673,633822886984823975214363968001,323885966298342689179026460989868,2417842429535473200466308,2413138481558843201995874,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord524 : orderSearch 7 7 324518551245297441980164008661673 [324518551245297441980164008661673,323885963880500264155966194405544,633822886984823975214363968001,323885966298342689179026460989868,2417842429535473200466308,2413138481558843201995874,324517315718387453247965072892240] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord525 : orderSearch 7 7 324518551240575105321523598324216 [324518551240575105321523598324216,323885963880500264155966194405544,324517315718387453247965072892240,323885966298342689179026460989868,2417842429535473200466308,633822886984823975214363968001,2413138481558843201995874] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord526 : orderSearch 7 7 324518551245297447902705984381777 [324518551245297447902705984381777,633822886984823975214363968001,324517315718387453247965072892240,323885966298342689179026460989868,2417842429535473200466308,323885963880500264155966194405544,2413138481558843201995874] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord527 : orderSearch 7 7 324517318131525932550601807947122 [324517318131525932550601807947122,2413138481558843201995874,324517315718387453247965072892240,323885966298342689179026460989868,2417842429535473200466308,323885963880500264155966194405544,633822886984823975214363968001] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord528 : orderSearch 8 8 323885966298342689179026460989868 [323885966298342689179026460989868,2417842429535473200466308,323885963880500264155966194405544,633822886984823975214363968001,2413138481558843201995874,324517315718387453247965072892240] = false := by
  apply ocover_step (states := [(7,1235526900789261849340149760,[1235526900789261849340149760,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544,2413138481558843201995874,324517315718387453247965072892240]),(7,1235526900789261849340149760,[1235526900789261849340149760,323885966298342689179026460989868,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544,2413138481558843201995874,324517315718387453247965072892240]),(7,324518553658426723892391484808109,[324518553658426723892391484808109,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544,2413138481558843201995874,324517315718387453247965072892240]),(7,324518553658426723892391484808109,[324518553658426723892391484808109,323885966298342689179026460989868,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544,2413138481558843201995874,324517315718387453247965072892240]),(7,2413129273874491937669152,[2413129273874491937669152,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544,633822886984823975214363968001,324517315718387453247965072892240]),(7,2413129273874491937669152,[2413129273874491937669152,323885966298342689179026460989868,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544,633822886984823975214363968001,324517315718387453247965072892240]),(7,323885966298351896863377725316590,[323885966298351896863377725316590,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544,633822886984823975214363968001,324517315718387453247965072892240]),(7,323885966298351896863377725316590,[323885966298351896863377725316590,323885966298342689179026460989868,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544,633822886984823975214363968001,324517315718387453247965072892240]),(7,323884728358312621107233536737536,[323884728358312621107233536737536,324517315718387453247965072892240,2417842429535473200466308,323885963880500264155966194405544,633822886984823975214363968001,2413138481558843201995874]),(7,323884728358312621107233536737536,[323884728358312621107233536737536,323885966298342689179026460989868,324517315718387453247965072892240,2417842429535473200466308,323885963880500264155966194405544,633822886984823975214363968001,2413138481558843201995874]),(7,324518553658417521319757997144572,[324518553658417521319757997144572,324517315718387453247965072892240,2417842429535473200466308,323885963880500264155966194405544,633822886984823975214363968001,2413138481558843201995874]),(7,324518553658417521319757997144572,[324518553658417521319757997144572,323885966298342689179026460989868,324517315718387453247965072892240,2417842429535473200466308,323885963880500264155966194405544,633822886984823975214363968001,2413138481558843201995874]),(7,324517318136229873758612405594580,[324517318136229873758612405594580,324517315718387453247965072892240,323885966298342689179026460989868,323885963880500264155966194405544,633822886984823975214363968001,2413138481558843201995874]),(7,324517318136229873758612405594580,[324517318136229873758612405594580,2417842429535473200466308,324517315718387453247965072892240,323885966298342689179026460989868,323885963880500264155966194405544,633822886984823975214363968001,2413138481558843201995874]),(7,324518551245297441980164008661673,[324518551245297441980164008661673,633822886984823975214363968001,323885966298342689179026460989868,2417842429535473200466308,2413138481558843201995874,324517315718387453247965072892240]),(7,324518551245297441980164008661673,[324518551245297441980164008661673,323885963880500264155966194405544,633822886984823975214363968001,323885966298342689179026460989868,2417842429535473200466308,2413138481558843201995874,324517315718387453247965072892240]),(7,324518551240575105321523598324216,[324518551240575105321523598324216,323885963880500264155966194405544,324517315718387453247965072892240,323885966298342689179026460989868,2417842429535473200466308,633822886984823975214363968001,2413138481558843201995874]),(7,324518551245297447902705984381777,[324518551245297447902705984381777,633822886984823975214363968001,324517315718387453247965072892240,323885966298342689179026460989868,2417842429535473200466308,323885963880500264155966194405544,2413138481558843201995874]),(7,324517318131525932550601807947122,[324517318131525932550601807947122,2413138481558843201995874,324517315718387453247965072892240,323885966298342689179026460989868,2417842429535473200466308,323885963880500264155966194405544,633822886984823975214363968001])])
  · decide +kernel
  · simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.not_false, ord509, ord510, ord511, ord512, ord513, ord514, ord515, ord516, ord517, ord518, ord519, ord520, ord521, ord522, ord523, ord524, ord525, ord526, ord527]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord529 : orderSearch 8 8 9024825867763968 [9024825867763968,2417842429535473200466308,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord530 : orderSearch 7 7 632587364787972431306242916352 [632587364787972431306242916352,633822886984823975214363968001,2417842429535473200466308,324517315718387453247965072892240,2413138481558843201995874,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord531 : orderSearch 7 7 632587364787972431306242916352 [632587364787972431306242916352,324517318136229873758612405594580,633822886984823975214363968001,2417842429535473200466308,324517315718387453247965072892240,2413138481558843201995874,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord532 : orderSearch 7 7 324518553658426725302520526646229 [324518553658426725302520526646229,633822886984823975214363968001,2417842429535473200466308,324517315718387453247965072892240,2413138481558843201995874,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord533 : orderSearch 7 7 324518553658426725302520526646229 [324518553658426725302520526646229,324517318136229873758612405594580,633822886984823975214363968001,2417842429535473200466308,324517315718387453247965072892240,2413138481558843201995874,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord534 : orderSearch 7 7 2413129275002595171139648 [2413129275002595171139648,2413138481558843201995874,2417842429535473200466308,324517315718387453247965072892240,633822886984823975214363968001,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord535 : orderSearch 7 7 2413129275002595171139648 [2413129275002595171139648,324517318136229873758612405594580,2413138481558843201995874,2417842429535473200466308,324517315718387453247965072892240,633822886984823975214363968001,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord536 : orderSearch 7 7 324517318136239080314860436450806 [324517318136239080314860436450806,2413138481558843201995874,2417842429535473200466308,324517315718387453247965072892240,633822886984823975214363968001,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord537 : orderSearch 7 7 324517318136239080314860436450806 [324517318136239080314860436450806,324517318136229873758612405594580,2413138481558843201995874,2417842429535473200466308,324517315718387453247965072892240,633822886984823975214363968001,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord538 : orderSearch 7 7 323884728358312616594820602855552 [323884728358312616594820602855552,323885963880500264155966194405544,2417842429535473200466308,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord539 : orderSearch 7 7 323884728358312616594820602855552 [323884728358312616594820602855552,324517318136229873758612405594580,323885963880500264155966194405544,2417842429535473200466308,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord540 : orderSearch 7 7 324518553658417521319757997144572 [324518553658417521319757997144572,323885963880500264155966194405544,2417842429535473200466308,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord541 : orderSearch 7 7 324518553658417521319757997144572 [324518553658417521319757997144572,324517318136229873758612405594580,323885963880500264155966194405544,2417842429535473200466308,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord542 : orderSearch 7 7 324518551245297447902705984381777 [324518551245297447902705984381777,633822886984823975214363968001,324517318136229873758612405594580,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord543 : orderSearch 7 7 324518551245297447902705984381777 [324518551245297447902705984381777,324517315718387453247965072892240,633822886984823975214363968001,324517318136229873758612405594580,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord544 : orderSearch 7 7 324518551240575105321523598324216 [324518551240575105321523598324216,324517315718387453247965072892240,323885963880500264155966194405544,324517318136229873758612405594580,2417842429535473200466308,633822886984823975214363968001,2413138481558843201995874] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord545 : orderSearch 7 7 324518551245297441980164008661673 [324518551245297441980164008661673,633822886984823975214363968001,323885963880500264155966194405544,324517318136229873758612405594580,2417842429535473200466308,324517315718387453247965072892240,2413138481558843201995874] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord546 : orderSearch 8 8 324517318136229873758612405594580 [324517318136229873758612405594580,2417842429535473200466308,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544] = false := by
  apply ocover_step (states := [(7,632587364787972431306242916352,[632587364787972431306242916352,633822886984823975214363968001,2417842429535473200466308,324517315718387453247965072892240,2413138481558843201995874,323885963880500264155966194405544]),(7,632587364787972431306242916352,[632587364787972431306242916352,324517318136229873758612405594580,633822886984823975214363968001,2417842429535473200466308,324517315718387453247965072892240,2413138481558843201995874,323885963880500264155966194405544]),(7,324518553658426725302520526646229,[324518553658426725302520526646229,633822886984823975214363968001,2417842429535473200466308,324517315718387453247965072892240,2413138481558843201995874,323885963880500264155966194405544]),(7,324518553658426725302520526646229,[324518553658426725302520526646229,324517318136229873758612405594580,633822886984823975214363968001,2417842429535473200466308,324517315718387453247965072892240,2413138481558843201995874,323885963880500264155966194405544]),(7,2413129275002595171139648,[2413129275002595171139648,2413138481558843201995874,2417842429535473200466308,324517315718387453247965072892240,633822886984823975214363968001,323885963880500264155966194405544]),(7,2413129275002595171139648,[2413129275002595171139648,324517318136229873758612405594580,2413138481558843201995874,2417842429535473200466308,324517315718387453247965072892240,633822886984823975214363968001,323885963880500264155966194405544]),(7,324517318136239080314860436450806,[324517318136239080314860436450806,2413138481558843201995874,2417842429535473200466308,324517315718387453247965072892240,633822886984823975214363968001,323885963880500264155966194405544]),(7,324517318136239080314860436450806,[324517318136239080314860436450806,324517318136229873758612405594580,2413138481558843201995874,2417842429535473200466308,324517315718387453247965072892240,633822886984823975214363968001,323885963880500264155966194405544]),(7,323884728358312616594820602855552,[323884728358312616594820602855552,323885963880500264155966194405544,2417842429535473200466308,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874]),(7,323884728358312616594820602855552,[323884728358312616594820602855552,324517318136229873758612405594580,323885963880500264155966194405544,2417842429535473200466308,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874]),(7,324518553658417521319757997144572,[324518553658417521319757997144572,323885963880500264155966194405544,2417842429535473200466308,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874]),(7,324518553658417521319757997144572,[324518553658417521319757997144572,324517318136229873758612405594580,323885963880500264155966194405544,2417842429535473200466308,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874]),(7,324518551245297447902705984381777,[324518551245297447902705984381777,633822886984823975214363968001,324517318136229873758612405594580,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544]),(7,324518551245297447902705984381777,[324518551245297447902705984381777,324517315718387453247965072892240,633822886984823975214363968001,324517318136229873758612405594580,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544]),(7,324518551240575105321523598324216,[324518551240575105321523598324216,324517315718387453247965072892240,323885963880500264155966194405544,324517318136229873758612405594580,2417842429535473200466308,633822886984823975214363968001,2413138481558843201995874]),(7,324518551245297441980164008661673,[324518551245297441980164008661673,633822886984823975214363968001,323885963880500264155966194405544,324517318136229873758612405594580,2417842429535473200466308,324517315718387453247965072892240,2413138481558843201995874])])
  · decide +kernel
  · simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.not_false, ord530, ord531, ord532, ord533, ord534, ord535, ord536, ord537, ord538, ord539, ord540, ord541, ord542, ord543, ord544, ord545]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord547 : orderSearch 7 7 0 [0,633822886984823975214363968001,323885963880500264155966194405544,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord548 : orderSearch 7 7 0 [0,323884728358312612082407668973568,633822886984823975214363968001,323885963880500264155966194405544,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord549 : orderSearch 7 6 324518551245297436057622032941569 [324518551245297436057622032941569,323885963880500264155966194405544,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord550 : orderSearch 7 6 324518551245297436057622032941569 [324518551245297436057622032941569,323884728358312612082407668973568,323885963880500264155966194405544,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord551 : orderSearch 7 6 324518551245297436057622032941569 [324518551245297436057622032941569,633822886984823975214363968001,323885963880500264155966194405544,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord552 : orderSearch 7 6 324518551245297436057622032941569 [324518551245297436057622032941569,323884728358312612082407668973568,633822886984823975214363968001,323885963880500264155966194405544,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord553 : orderSearch 7 7 0 [0,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240,633822886984823975214363968001,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord554 : orderSearch 7 7 0 [0,323884728358312612082407668973568,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240,633822886984823975214363968001,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord555 : orderSearch 7 6 323884730771451093641250870969442 [323884730771451093641250870969442,323885963880500264155966194405544,324517315718387453247965072892240,633822886984823975214363968001,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord556 : orderSearch 7 6 323884730771451093641250870969442 [323884730771451093641250870969442,323884728358312612082407668973568,323885963880500264155966194405544,324517315718387453247965072892240,633822886984823975214363968001,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord557 : orderSearch 7 6 323884730771451093641250870969442 [323884730771451093641250870969442,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240,633822886984823975214363968001,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord558 : orderSearch 7 6 323884730771451093641250870969442 [323884730771451093641250870969442,323884728358312612082407668973568,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240,633822886984823975214363968001,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord559 : orderSearch 7 7 0 [0,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord560 : orderSearch 7 7 0 [0,323884728358312612082407668973568,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord561 : orderSearch 7 6 323884730776155041617880869439876 [323884730776155041617880869439876,323885963880500264155966194405544,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord562 : orderSearch 7 6 323884730776155041617880869439876 [323884730776155041617880869439876,323884728358312612082407668973568,323885963880500264155966194405544,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord563 : orderSearch 7 6 323884730776155041617880869439876 [323884730776155041617880869439876,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord564 : orderSearch 7 6 323884730776155041617880869439876 [323884730776155041617880869439876,323884728358312612082407668973568,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord565 : orderSearch 7 7 324518551240575105321523598324216 [324518551240575105321523598324216,323884728358312612082407668973568,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord566 : orderSearch 7 7 324518551240575105321523598324216 [324518551240575105321523598324216,323885963880500264155966194405544,323884728358312612082407668973568,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord567 : orderSearch 7 7 324518551240575105321523598324216 [324518551240575105321523598324216,324517315718387453247965072892240,323884728358312612082407668973568,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord568 : orderSearch 7 7 324518551240575105321523598324216 [324518551240575105321523598324216,323885963880500264155966194405544,324517315718387453247965072892240,323884728358312612082407668973568,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord569 : orderSearch 7 7 324518551245297441980164008661673 [324518551245297441980164008661673,323885963880500264155966194405544,633822886984823975214363968001,323884728358312612082407668973568,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord570 : orderSearch 7 7 323885966293638744586706162930922 [323885966293638744586706162930922,2413138481558843201995874,323884728358312612082407668973568,324517315718387453247965072892240,633822886984823975214363968001,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord571 : orderSearch 7 7 323885966293638744586706162930922 [323885966293638744586706162930922,323885963880500264155966194405544,2413138481558843201995874,323884728358312612082407668973568,324517315718387453247965072892240,633822886984823975214363968001,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord572 : orderSearch 7 7 323885966298342689179026460989868 [323885966298342689179026460989868,2417842429535473200466308,323884728358312612082407668973568,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord573 : orderSearch 7 7 323885966298342689179026460989868 [323885966298342689179026460989868,323885963880500264155966194405544,2417842429535473200466308,323884728358312612082407668973568,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord574 : orderSearch 7 7 324518551245297447902705984381777 [324518551245297447902705984381777,324517315718387453247965072892240,633822886984823975214363968001,323884728358312612082407668973568,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord575 : orderSearch 7 7 324517318131525932550601807947122 [324517318131525932550601807947122,2413138481558843201995874,323884728358312612082407668973568,323885963880500264155966194405544,633822886984823975214363968001,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord576 : orderSearch 7 7 324517318131525932550601807947122 [324517318131525932550601807947122,324517315718387453247965072892240,2413138481558843201995874,323884728358312612082407668973568,323885963880500264155966194405544,633822886984823975214363968001,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord577 : orderSearch 7 7 324517318136229873758612405594580 [324517318136229873758612405594580,2417842429535473200466308,323884728358312612082407668973568,323885963880500264155966194405544,633822886984823975214363968001,2413138481558843201995874] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord578 : orderSearch 7 7 324517318136229873758612405594580 [324517318136229873758612405594580,324517315718387453247965072892240,2417842429535473200466308,323884728358312612082407668973568,323885963880500264155966194405544,633822886984823975214363968001,2413138481558843201995874] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord579 : orderSearch 8 8 323884728358312612082407668973568 [323884728358312612082407668973568,323885963880500264155966194405544,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308] = false := by
  apply ocover_step (states := [(7,0,[0,633822886984823975214363968001,323885963880500264155966194405544,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308]),(7,0,[0,323884728358312612082407668973568,633822886984823975214363968001,323885963880500264155966194405544,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308]),(6,324518551245297436057622032941569,[324518551245297436057622032941569,323885963880500264155966194405544,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308]),(6,324518551245297436057622032941569,[324518551245297436057622032941569,323884728358312612082407668973568,323885963880500264155966194405544,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308]),(6,324518551245297436057622032941569,[324518551245297436057622032941569,633822886984823975214363968001,323885963880500264155966194405544,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308]),(6,324518551245297436057622032941569,[324518551245297436057622032941569,323884728358312612082407668973568,633822886984823975214363968001,323885963880500264155966194405544,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308]),(7,0,[0,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240,633822886984823975214363968001,2417842429535473200466308]),(7,0,[0,323884728358312612082407668973568,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240,633822886984823975214363968001,2417842429535473200466308]),(6,323884730771451093641250870969442,[323884730771451093641250870969442,323885963880500264155966194405544,324517315718387453247965072892240,633822886984823975214363968001,2417842429535473200466308]),(6,323884730771451093641250870969442,[323884730771451093641250870969442,323884728358312612082407668973568,323885963880500264155966194405544,324517315718387453247965072892240,633822886984823975214363968001,2417842429535473200466308]),(6,323884730771451093641250870969442,[323884730771451093641250870969442,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240,633822886984823975214363968001,2417842429535473200466308]),(6,323884730771451093641250870969442,[323884730771451093641250870969442,323884728358312612082407668973568,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240,633822886984823975214363968001,2417842429535473200466308]),(7,0,[0,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874]),(7,0,[0,323884728358312612082407668973568,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874]),(6,323884730776155041617880869439876,[323884730776155041617880869439876,323885963880500264155966194405544,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874]),(6,323884730776155041617880869439876,[323884730776155041617880869439876,323884728358312612082407668973568,323885963880500264155966194405544,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874]),(6,323884730776155041617880869439876,[323884730776155041617880869439876,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874]),(6,323884730776155041617880869439876,[323884730776155041617880869439876,323884728358312612082407668973568,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874]),(7,324518551240575105321523598324216,[324518551240575105321523598324216,323884728358312612082407668973568,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308]),(7,324518551240575105321523598324216,[324518551240575105321523598324216,323885963880500264155966194405544,323884728358312612082407668973568,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308]),(7,324518551240575105321523598324216,[324518551240575105321523598324216,324517315718387453247965072892240,323884728358312612082407668973568,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308]),(7,324518551240575105321523598324216,[324518551240575105321523598324216,323885963880500264155966194405544,324517315718387453247965072892240,323884728358312612082407668973568,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308]),(7,324518551245297441980164008661673,[324518551245297441980164008661673,323885963880500264155966194405544,633822886984823975214363968001,323884728358312612082407668973568,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308]),(7,323885966293638744586706162930922,[323885966293638744586706162930922,2413138481558843201995874,323884728358312612082407668973568,324517315718387453247965072892240,633822886984823975214363968001,2417842429535473200466308]),(7,323885966293638744586706162930922,[323885966293638744586706162930922,323885963880500264155966194405544,2413138481558843201995874,323884728358312612082407668973568,324517315718387453247965072892240,633822886984823975214363968001,2417842429535473200466308]),(7,323885966298342689179026460989868,[323885966298342689179026460989868,2417842429535473200466308,323884728358312612082407668973568,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874]),(7,323885966298342689179026460989868,[323885966298342689179026460989868,323885963880500264155966194405544,2417842429535473200466308,323884728358312612082407668973568,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874]),(7,324518551245297447902705984381777,[324518551245297447902705984381777,324517315718387453247965072892240,633822886984823975214363968001,323884728358312612082407668973568,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308]),(7,324517318131525932550601807947122,[324517318131525932550601807947122,2413138481558843201995874,323884728358312612082407668973568,323885963880500264155966194405544,633822886984823975214363968001,2417842429535473200466308]),(7,324517318131525932550601807947122,[324517318131525932550601807947122,324517315718387453247965072892240,2413138481558843201995874,323884728358312612082407668973568,323885963880500264155966194405544,633822886984823975214363968001,2417842429535473200466308]),(7,324517318136229873758612405594580,[324517318136229873758612405594580,2417842429535473200466308,323884728358312612082407668973568,323885963880500264155966194405544,633822886984823975214363968001,2413138481558843201995874]),(7,324517318136229873758612405594580,[324517318136229873758612405594580,324517315718387453247965072892240,2417842429535473200466308,323884728358312612082407668973568,323885963880500264155966194405544,633822886984823975214363968001,2413138481558843201995874])])
  · decide +kernel
  · simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.not_false, ord547, ord548, ord549, ord550, ord551, ord552, ord553, ord554, ord555, ord556, ord557, ord558, ord559, ord560, ord561, ord562, ord563, ord564, ord565, ord566, ord567, ord568, ord569, ord570, ord571, ord572, ord573, ord574, ord575, ord576, ord577, ord578]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord580 : orderSearch 7 7 633822882262475471490002190336 [633822882262475471490002190336,633822886984823975214363968001,323885963880500264155966194405544,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord581 : orderSearch 7 7 633822882262475471490002190336 [633822882262475471490002190336,324518551240575105321523598324216,633822886984823975214363968001,323885963880500264155966194405544,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord582 : orderSearch 7 7 324518551245297453825247960101881 [324518551245297453825247960101881,633822886984823975214363968001,323885963880500264155966194405544,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord583 : orderSearch 7 7 324518551245297453825247960101881 [324518551245297453825247960101881,324518551240575105321523598324216,633822886984823975214363968001,323885963880500264155966194405544,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord584 : orderSearch 7 7 3384309700411488 [3384309700411488,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240,633822886984823975214363968001,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord585 : orderSearch 7 7 3384309700411488 [3384309700411488,324518551240575105321523598324216,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240,633822886984823975214363968001,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord586 : orderSearch 7 7 324518553653713583496057099908602 [324518553653713583496057099908602,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240,633822886984823975214363968001,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord587 : orderSearch 7 7 324518553653713583496057099908602 [324518553653713583496057099908602,324518551240575105321523598324216,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240,633822886984823975214363968001,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord588 : orderSearch 7 7 13537238801645952 [13537238801645952,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord589 : orderSearch 7 7 13537238801645952 [13537238801645952,324518551240575105321523598324216,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord590 : orderSearch 7 7 324518553658417521319757997144572 [324518553658417521319757997144572,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord591 : orderSearch 7 7 324518553658417521319757997144572 [324518553658417521319757997144572,324518551240575105321523598324216,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord592 : orderSearch 7 7 324518551245297441980164008661673 [324518551245297441980164008661673,633822886984823975214363968001,324518551240575105321523598324216,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord593 : orderSearch 7 7 324518551245297441980164008661673 [324518551245297441980164008661673,323885963880500264155966194405544,633822886984823975214363968001,324518551240575105321523598324216,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord594 : orderSearch 7 7 324518551245297447902705984381777 [324518551245297447902705984381777,633822886984823975214363968001,324518551240575105321523598324216,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord595 : orderSearch 7 7 324518551245297447902705984381777 [324518551245297447902705984381777,324517315718387453247965072892240,633822886984823975214363968001,324518551240575105321523598324216,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308] = false := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord596 : orderSearch 8 8 324518551240575105321523598324216 [324518551240575105321523598324216,323885963880500264155966194405544,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308] = false := by
  apply ocover_step (states := [(7,633822882262475471490002190336,[633822882262475471490002190336,633822886984823975214363968001,323885963880500264155966194405544,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308]),(7,633822882262475471490002190336,[633822882262475471490002190336,324518551240575105321523598324216,633822886984823975214363968001,323885963880500264155966194405544,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308]),(7,324518551245297453825247960101881,[324518551245297453825247960101881,633822886984823975214363968001,323885963880500264155966194405544,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308]),(7,324518551245297453825247960101881,[324518551245297453825247960101881,324518551240575105321523598324216,633822886984823975214363968001,323885963880500264155966194405544,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308]),(7,3384309700411488,[3384309700411488,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240,633822886984823975214363968001,2417842429535473200466308]),(7,3384309700411488,[3384309700411488,324518551240575105321523598324216,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240,633822886984823975214363968001,2417842429535473200466308]),(7,324518553653713583496057099908602,[324518553653713583496057099908602,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240,633822886984823975214363968001,2417842429535473200466308]),(7,324518553653713583496057099908602,[324518553653713583496057099908602,324518551240575105321523598324216,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240,633822886984823975214363968001,2417842429535473200466308]),(7,13537238801645952,[13537238801645952,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874]),(7,13537238801645952,[13537238801645952,324518551240575105321523598324216,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874]),(7,324518553658417521319757997144572,[324518553658417521319757997144572,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874]),(7,324518553658417521319757997144572,[324518553658417521319757997144572,324518551240575105321523598324216,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874]),(7,324518551245297441980164008661673,[324518551245297441980164008661673,633822886984823975214363968001,324518551240575105321523598324216,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308]),(7,324518551245297441980164008661673,[324518551245297441980164008661673,323885963880500264155966194405544,633822886984823975214363968001,324518551240575105321523598324216,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308]),(7,324518551245297447902705984381777,[324518551245297447902705984381777,633822886984823975214363968001,324518551240575105321523598324216,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308]),(7,324518551245297447902705984381777,[324518551245297447902705984381777,324517315718387453247965072892240,633822886984823975214363968001,324518551240575105321523598324216,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308])])
  · decide +kernel
  · simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.not_false, ord580, ord581, ord582, ord583, ord584, ord585, ord586, ord587, ord588, ord589, ord590, ord591, ord592, ord593, ord594, ord595]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem ord597 : orderSearch 9 9 0 [633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240] = false := by
  apply ocover_step (states := [(8,9205357638345293824,[9205357638345293824,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240]),(8,633825300114100176419220670051,[633825300114100176419220670051,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544,324517315718387453247965072892240]),(8,4713143110832790437888,[4713143110832790437888,633822886984823975214363968001,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240]),(8,633825300114110399854773996421,[633825300114110399854773996421,633822886984823975214363968001,2417842429535473200466308,2413138481558843201995874,323885963880500264155966194405544,324517315718387453247965072892240]),(8,1235522187646151016549711872,[1235522187646151016549711872,633822886984823975214363968001,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308,324517315718387453247965072892240]),(8,324518551245297441980164008661673,[324518551245297441980164008661673,633822886984823975214363968001,323885963880500264155966194405544,2413138481558843201995874,2417842429535473200466308,324517315718387453247965072892240]),(8,632587360074829320473452478464,[632587360074829320473452478464,633822886984823975214363968001,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544]),(8,324518551245297447902705984381777,[324518551245297447902705984381777,633822886984823975214363968001,324517315718387453247965072892240,2413138481558843201995874,2417842429535473200466308,323885963880500264155966194405544]),(8,2413129272746388704198656,[2413129272746388704198656,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001,323885963880500264155966194405544,324517315718387453247965072892240]),(8,2417851638347927698263526,[2417851638347927698263526,2413138481558843201995874,2417842429535473200466308,633822886984823975214363968001,323885963880500264155966194405544,324517315718387453247965072892240]),(8,1128103233470496,[1128103233470496,2413138481558843201995874,323885963880500264155966194405544,633822886984823975214363968001,2417842429535473200466308,324517315718387453247965072892240]),(8,323885966293638744586706162930922,[323885966293638744586706162930922,2413138481558843201995874,323885963880500264155966194405544,633822886984823975214363968001,2417842429535473200466308,324517315718387453247965072892240]),(8,2256206466940992,[2256206466940992,2413138481558843201995874,324517315718387453247965072892240,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544]),(8,324517318131525932550601807947122,[324517318131525932550601807947122,2413138481558843201995874,324517315718387453247965072892240,633822886984823975214363968001,2417842429535473200466308,323885963880500264155966194405544]),(8,4512412933881984,[4512412933881984,2417842429535473200466308,323885963880500264155966194405544,633822886984823975214363968001,2413138481558843201995874,324517315718387453247965072892240]),(8,323885966298342689179026460989868,[323885966298342689179026460989868,2417842429535473200466308,323885963880500264155966194405544,633822886984823975214363968001,2413138481558843201995874,324517315718387453247965072892240]),(8,9024825867763968,[9024825867763968,2417842429535473200466308,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544]),(8,324517318136229873758612405594580,[324517318136229873758612405594580,2417842429535473200466308,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874,323885963880500264155966194405544]),(8,323884728358312612082407668973568,[323884728358312612082407668973568,323885963880500264155966194405544,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308]),(8,324518551240575105321523598324216,[324518551240575105321523598324216,323885963880500264155966194405544,324517315718387453247965072892240,633822886984823975214363968001,2413138481558843201995874,2417842429535473200466308])])
  · decide +kernel
  · simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.not_false, ord35, ord110, ord145, ord193, ord225, ord242, ord273, ord288, ord377, ord433, ord465, ord487, ord488, ord507, ord508, ord528, ord529, ord546, ord579, ord596]

theorem ordered_nine : ¬ Build 9 inputs.toFinset := by
  intro hb
  obtain ⟨t,ha,hk,ho⟩ := canon_exists hb
  have r := order_complete ha ho (ws := inputs) (fuel := 9) (budget := 9) (zero_head t) hk (by omega) rfl (by decide)
  exact Bool.noConfusion (ord597.symm.trans r)

end PEqualNP.Outside.L_meta_700_aux

namespace PEqualNP.Outside.L_meta_700_aux

theorem no_nine : ¬ Build 9 inputs.toFinset := ordered_nine

end PEqualNP.Outside.L_meta_700_aux

namespace PEqualNP.Outside.L_meta_700_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The test-mask gate simulation follows the official L-meta-719, which credits
-- jackboykin's L-meta-618 (PR 795). The singleton costs and indexed charges
-- below are specific to L-meta-700.
private def bridgeStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private abbrev Known (s : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = BitVec.allOnes 108 ∨ z ∈ s

private theorem maskRead (w : List W) (i : ℕ) (k : Fin 108) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

private theorem knownRead {s : Finset W} {w : List W} (h : ∀ z ∈ w, Known s z)
    (i : ℕ) : Known s (w.getD i 0) := by
  by_cases hi : i < w.length
  · apply h
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  · left
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt hi)]

private def FromGate (s : Finset W) (g : Gate) (z : W) : Prop :=
  Known s z ∨ ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧
    ((g.op = .and ∧ z = a &&& b) ∨ (g.op = .or ∧ z = a ||| b))

private theorem andKind {s : Finset W} {g : Gate} (hg : g.op = .and)
    {a b : W} (ha : Known s a) (hb : Known s b) : FromGate s g (a &&& b) := by
  rcases ha with rfl | rfl | ha
  · left; left; simp
  · rw [BitVec.allOnes_and]; exact .inl hb
  rcases hb with rfl | rfl | hb
  · left; left; simp
  · rw [BitVec.and_allOnes]; exact .inl (.inr (.inr ha))
  by_cases hab : a = b
  · subst b; rw [BitVec.and_self]; exact .inl (.inr (.inr ha))
  · exact .inr ⟨a, ha, b, hb, hab, .inl ⟨hg, rfl⟩⟩

private theorem orKind {s : Finset W} {g : Gate} (hg : g.op = .or)
    {a b : W} (ha : Known s a) (hb : Known s b) : FromGate s g (a ||| b) := by
  rcases ha with rfl | rfl | ha
  · rw [show (0 : W) ||| b = b by ext i hi; simp]; exact .inl hb
  · exact .inl (.inr (.inl BitVec.allOnes_or))
  rcases hb with rfl | rfl | hb
  · rw [show a ||| (0 : W) = a by ext i hi; simp]; exact .inl (.inr (.inr ha))
  · exact .inl (.inr (.inl BitVec.or_allOnes))
  by_cases hab : a = b
  · subst b; rw [BitVec.or_self]; exact .inl (.inr (.inr ha))
  · exact .inr ⟨a, ha, b, hb, hab, .inr ⟨hg, rfl⟩⟩

private theorem maskGate {s : Finset W} (w : List W) (hw : ∀ z ∈ w, Known s z)
    (g : Gate) (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∃ z, FromGate s g z ∧ ∀ k, bridgeStep (w.map (bit k)) g = (w ++ [z]).map (bit k) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or at hop
  change args.length ≤ 2 at hlen
  cases args with
  | nil =>
    rcases hop with rfl | rfl
    · refine ⟨BitVec.allOnes 108, .inl (.inr (.inl rfl)), ?_⟩
      intro k; simp [bridgeStep, GateOp.eval, bit, k.isLt]
      change (BitVec.allOnes 108)[k.val] = true
      simp only [BitVec.getElem_allOnes]
    · exact ⟨0, .inl (.inl rfl), by simp [bridgeStep, GateOp.eval, bit]⟩
  | cons i tail =>
    cases tail with
    | nil =>
      rcases hop with rfl | rfl
      · exact ⟨_, .inl (knownRead hw i),
          by simp only [bridgeStep, List.map_cons, List.map_nil, maskRead]; simp [GateOp.eval]⟩
      · exact ⟨_, .inl (knownRead hw i),
          by simp only [bridgeStep, List.map_cons, List.map_nil, maskRead]; simp [GateOp.eval]⟩
    | cons j tail =>
      cases tail with
      | cons => simp at hlen
      | nil =>
        rcases hop with rfl | rfl
        · exact ⟨_, andKind rfl (knownRead hw i) (knownRead hw j),
            by simp only [bridgeStep, List.map_cons, List.map_nil, maskRead]; simp [GateOp.eval, bit]⟩
        · exact ⟨_, orKind rfl (knownRead hw i) (knownRead hw j),
            by simp only [bridgeStep, List.map_cons, List.map_nil, maskRead]; simp [GateOp.eval, bit]⟩

private theorem oldWire (gs : List Gate) (w : List Bool) (i : ℕ) (v : Bool) (hi : i < w.length) :
    (gs.foldl bridgeStep w).getD i v = w.getD i v := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (bridgeStep w g) (by simp [bridgeStep]; omega)]
    exact List.getD_append _ _ _ _ hi

private def later (S : Finset ℕ) (j : ℕ) := S.filter (j ≤ ·)

private theorem later_count (S : Finset ℕ) (j : ℕ) :
    (later S (j+1)).card + (if j ∈ S then 1 else 0) = (later S j).card := by
  by_cases hj : j ∈ S
  · have eq : later S j = insert j (later S (j+1)) := by
      ext i
      simp only [later, Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hs, hle⟩
        by_cases eq : i = j
        · exact .inl eq
        · exact .inr ⟨hs, by omega⟩
      · rintro (rfl | ⟨hs, hle⟩)
        · exact ⟨hj, le_rfl⟩
        · exact ⟨hs, by omega⟩
    have hn : j ∉ later S (j+1) := by simp [later]
    rw [eq, Finset.card_insert_of_notMem hn]
    simp [hj]
  · have eq : later S j = later S (j+1) := by
      ext i
      simp [later]
      by_cases h : i = j
      · subst i; simp [hj]
      · omega
    rw [eq]
    simp [hj]

private def allowance (A B D : Finset ℕ) (j : ℕ) : ℕ :=
  (later A j).card + (later B j).card + 2 * (later D j).card

private theorem chargeEq (A B D : Finset ℕ) (j : ℕ) :
    allowance A B D (j+1) + (if j ∈ A then 1 else 0) +
      (if j ∈ B then 1 else 0) + 2*(if j ∈ D then 1 else 0) = allowance A B D j := by
  unfold allowance
  have a := later_count A j
  have b := later_count B j
  have d := later_count D j
  omega

private abbrev realWide (C : Circuit) (j : ℕ) : Prop :=
  ∃ u v : Fin 5, u ≠ v ∧
    (C.wires (List.ofFn (fun i : Fin 5 => decide (i = u)))).getD (5+j) false = true ∧
    (C.wires (List.ofFn (fun i : Fin 5 => decide (i = v)))).getD (5+j) false = true

theorem charged_build (Build : ℕ → Finset W → Prop)
    (done : ∀ {s}, goal ∈ s → Build 0 s)
    (weaken : ∀ {k l s}, k ≤ l → Build k s → Build l s)
    (andStep : ∀ {k s a b}, a ∈ s → b ∈ s → a ≠ b →
      Build k (insert (a &&& b) s) → Build (k+1) s)
    (orStep : ∀ {k s a b}, a ∈ s → b ∈ s → a ≠ b →
      Build k (insert (a ||| b) s) → Build (k+(if isWide (a ||| b) then 1 else 2)) s)
    (C : Circuit) (A B D : Finset ℕ) (hmono : Monotone2 C)
    (he : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 5, (u.val, v.val) ∈ edges ∧ x u = true ∧ x v = true)
    (hA : ∀ j g, C.gates[j]? = some g → g.op = .and → j ∈ A)
    (hB : ∀ j g, C.gates[j]? = some g → g.op = .or → realWide C j → j ∈ B)
    (hD : ∀ j g, C.gates[j]? = some g → g.op = .or → ¬ realWide C j → j ∈ D) :
    Build (A.card + B.card + 2*D.card) inputs.toFinset := by
  have goalVal (k : Fin 108) :
      (C.wires (List.ofFn (assignment k))).getD C.output false = bit k goal :=
    Bool.eq_iff_iff.mpr ((he (assignment k)).trans (graph_rows k))
  have go (gs : List Gate) (j : ℕ) (w : List W) (s : Finset W)
      (ix : ∀ t g, gs[t]? = some g → C.gates[j+t]? = some g)
      (hlen : w.length = 5+j) (hw : ∀ z ∈ w, Known s z)
      (hrows : ∀ k, C.wires (List.ofFn (assignment k)) = gs.foldl bridgeStep (w.map (bit k))) :
      Build (allowance A B D j) s := by
    induction gs generalizing j w s with
    | nil =>
      have zgoal : w.getD C.output 0 = goal := by
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        have h := goalVal ⟨i,hi⟩
        rw [hrows, List.foldl_nil, maskRead] at h
        exact h
      have hz := knownRead hw C.output
      rw [zgoal] at hz
      rcases hz with h | h | h
      · exact False.elim ((by decide : goal ≠ (0 : W)) h)
      · exact False.elim ((by decide : goal ≠ BitVec.allOnes 108) h)
      · exact weaken (Nat.zero_le _) (done h)
    | cons g gs ih =>
      have hj : C.gates[j]? = some g := by simpa using ix 0 g (by simp)
      have ok := hmono g (List.mem_of_getElem? hj)
      obtain ⟨z,hkind,hstep⟩ := maskGate w hw g ok
      have ht (t : ℕ) (g' : Gate) (hh : gs[t]? = some g') : C.gates[(j+1)+t]? = some g' := by
        simpa [Nat.add_assoc, Nat.add_comm 1 t] using ix (t+1) g' (by simpa using hh)
      have hlen' : (w ++ [z]).length = 5+(j+1) := by simp; omega
      have rows' (k : Fin 108) :
          C.wires (List.ofFn (assignment k)) = gs.foldl bridgeStep ((w++[z]).map (bit k)) := by
        rw [hrows, List.foldl_cons, hstep]
      have single (u : Fin 5) : (C.wires (List.ofFn (fun i : Fin 5 => decide (i=u)))).getD
            (5+j) false = z.getLsbD u.val := by
        let k : Fin 108 := ⟨u.val, by omega⟩
        rw [← single_rows u, rows']
        rw [oldWire gs _ (5+j) false (by simp; omega), maskRead]
        have ixz : (w ++ [z]).getD (5+j) 0 = z := by
          rw [← hlen, List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _)]
          simp
        rw [ixz]
        rfl
      have wideEq : realWide C j ↔ wide z := by simp only [realWide, wide, single]
      have eq := chargeEq A B D j
      have le : allowance A B D (j+1) ≤ allowance A B D j := by omega
      have old (hz : Known s z) : Build (allowance A B D j) s := by
        apply weaken le (ih (j+1) (w++[z]) s ht hlen' ?_ rows')
        intro u hu
        rcases List.mem_append.mp hu with a | b
        · exact hw _ a
        · simpa using (List.mem_singleton.mp b) ▸ hz
      have extend (a b : W) (ha : a ∈ s) (hb : b ∈ s) (hne : a ≠ b) :
          Build (allowance A B D (j+1)) (insert z s) := by
        apply ih (j+1) (w++[z]) (insert z s) ht hlen' ?_ rows'
        intro u hu
        rcases List.mem_append.mp hu with a | b
        · exact (hw u a).imp_right (Or.imp_right (Finset.mem_insert_of_mem ·))
        · rw [List.mem_singleton.mp b]; exact .inr (.inr (Finset.mem_insert_self _ _))
      rcases hkind with known | ⟨a,ha,b,hb,hab,⟨hop,hz⟩ | ⟨hop,hz⟩⟩
      · exact old known
      · have ha' := hA j g hj hop
        simp [ha'] at eq
        have tail := extend a b ha hb hab
        rw [hz] at tail
        exact weaken (by omega) (andStep ha hb hab tail)
      · have tail := extend a b ha hb hab
        rw [hz] at tail
        apply weaken _ (orStep ha hb hab tail)
        by_cases wi : wide z
        · have hmemPrime := hB j g hj hop (wideEq.mpr wi)
          simp [hmemPrime] at eq
          have wCost : isWide (a ||| b) = true := by simpa [isWide, ← hz] using wi
          rw [wCost]; simp; omega
        · have hmemPrime := hD j g hj hop (fun h => wi (wideEq.mp h))
          simp [hmemPrime] at eq
          have wCost : isWide (a ||| b) = false := by simpa [isWide, ← hz] using wi
          rw [wCost]; simp; omega
  have hfinal := go C.gates 0 rawInputs inputs.toFinset (by simp) (by decide)
    (fun z hz => Or.inr (Or.inr (List.mem_toFinset.mpr hz))) (by
      intro k; rw [input_rows]; rfl)
  simpa [allowance, later] using hfinal

end PEqualNP.Outside.L_meta_700_aux

open PEqualNP.Outside.L_meta_700_aux in
theorem PEqualNP.Outside.L_meta_700 : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (A B D : Finset ℕ), PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 5 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 5, (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (0, 4), (3, 4)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) → (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A) → (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.or → (∃ u v : Fin 5, u ≠ v ∧ (C.wires (List.ofFn (fun i : Fin 5 => decide (i = u)))).getD (5 + j) false = true ∧ (C.wires (List.ofFn (fun i : Fin 5 => decide (i = v)))).getD (5 + j) false = true) → j ∈ B) → (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.or → ¬ (∃ u v : Fin 5, u ≠ v ∧ (C.wires (List.ofFn (fun i : Fin 5 => decide (i = u)))).getD (5 + j) false = true ∧ (C.wires (List.ofFn (fun i : Fin 5 => decide (i = v)))).getD (5 + j) false = true) → j ∈ D) → 10 ≤ A.card + B.card + 2 * D.card := by
  intro C A B D hm he hA hB hD
  by_contra! h
  have hp := charged_build Build build_done build_weaken build_and build_or C A B D hm he hA hB hD
  exact no_nine (build_weaken (by omega) hp)
