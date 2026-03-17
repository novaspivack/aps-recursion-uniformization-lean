# SPEC_V5 — Countermodel Program for the Recursion–Composition Separation

**Location:** `project_history/SPEC_V5.md`

**Resolution:** **ACHIEVED.** The countermodel `sepAPS` in `Separation.lean` proves ∃ aps (I_rec(aps) ∧ ¬I_comp(aps)). 0 axioms, 0 sorry. See [FINAL_STATUS_AND_HANDOFF.md](../FINAL_STATUS_AND_HANDOFF.md) for the canonical resolution and §9a for the clean countermodel narrative.

---

## Goal

$$\exists\;\mathsf{aps}\;(\;I_{\mathrm{rec}}(\mathsf{aps})\ \wedge\ \neg I_{\mathrm{comp}}(\mathsf{aps})\;)$$

## Why now (historical)

T6 is false (`T6Counterexample.lean`, 0 sorry). The Baire route — the strongest positive attack — was structurally broken, not merely incomplete. Every other positive route (section surjectivity, gluing, failure-set intersection) collapses onto the same missing transport principle. The evidence has shifted toward separation.

---

# 0. The finite model autopsy (Workstream C1)

## The N=4, M=16 model

```
φ_0 = ⊥ (totally undefined)
φ_1 = [0,3,0,3,⊥,⊥,⊥,⊥,⊥,⊥,⊥,⊥,⊥,⊥,⊥,⊥]  (partial)
φ_2 = [0,3,⊥,⊥,⊥,⊥,⊥,⊥,⊥,⊥,⊥,⊥,⊥,⊥,⊥,⊥]  (partial)
φ_3 = [0,3,0,3,0,0,0,3,0,3,3,3,0,3,0,3]          (total, non-constant)

smn = [[0,0,0,0],[2,2,0,0],[2,0,0,0],[1,1,1,1]]
```

## Mechanism extraction

### Why I_rec holds

**Diagonal:** smn(0,0)=0, smn(1,1)=2, smn(2,2)=0, smn(3,3)=1.

Only 4 functions h qualify (have representable diagonal). All 4 satisfy h(0)=0. Since φ_0 = ⊥ and φ_{h(0)} = φ_0 = ⊥, index e=0 is a fixed point for all of them.

**The mechanism:** ⊥ is a universal trivial fixed point. φ_0 = ⊥ = φ_c for any c with φ_c = ⊥. Since h(0) = 0 for all qualifying h, and φ_0 = ⊥ = φ_0, we always have φ_e = φ_{h(e)} at e=0.

### Why I_comp fails

φ_3 is total and non-constant. As h: h(0)=0, h(1)=3. A tracker k needs:
- φ_k(⟨0,n⟩) = φ_0(n) = ⊥ for all n
- φ_k(⟨1,n⟩) = φ_3(n) which is defined

No k can be both undefined at ⟨0,·⟩ and defined at ⟨1,·⟩.

### The key structural features

1. **⊥ absorbs all qualifying h at index 0** — universal trivial fixed point
2. **Qualifying h is constrained by the diagonal** — only 4 out of 4^4 = 256 functions qualify
3. **The diagonal range misses the non-constant index** — smn(x,x) ∈ {0,1,2}, never 3
4. **Partiality creates the I_comp obstruction** — mixing ⊥ and defined values

### What breaks in the infinite extension

In an infinite APS, h = const_c qualifies for every c (if constants are representable). The fixed point of const_c needs e with φ_e = φ_c. If c ≠ 0, this requires a non-⊥ fixed point. The ⊥ trick no longer suffices.

**The precise failure:** h = const_1 maps 0 to 1. φ_0 = ⊥ ≠ φ_1. So e=0 is not a fixed point. We need e with φ_e = φ_1. If φ_1 is non-trivial, this forces a non-trivial extensional copy of φ_1. Accumulating such copies for all c generates richness.

---

# 1. The design constraints

## What the countermodel must satisfy

1. **smn_spec:** φ(smn(e,x))(n) = φ_e(⟨x,n⟩)
2. **I_rec:** ∀ h, representable diagonal ⇒ ∃ e, φ_e ≃ φ_{h(e)}
3. **¬I_comp:** ∃ representable h₀, ¬∃ k, ∀ x n, φ_k(⟨x,n⟩) = φ_{h₀(x)}(n)
4. **Non-trivial:** At least one non-constant representable function

## The fundamental tension

- I_rec needs fixed points for all qualifying h, including h = const_c
- h = const_c forces extensional copies of every index
- Extensional copies + smn structure may force I_comp

## The needle to thread

**Extensional richness without sectional richness.** The APS must have enough extensional classes for fixed points, but the section map k ↦ smn(k,x₀) must NOT be surjective onto all classes.

---

# 2. The architecture: sectional poverty

## The key idea

In standard computability, smn is surjective because the universal Turing machine can simulate any program with a curried first argument. In an abstract APS, smn need not be surjective.

**Design principle:** Make φ_e "binary" (depends on both arguments of the pair) for very few indices. Most indices compute functions that depend on only one component of the input, or are constant. The sections smn(e,x) then produce a restricted family.

## Concrete architecture

### Extensional classes

- **Class ⊥:** totally undefined (φ_e = ⊥)
- **Class C_c** for each c ∈ ℕ: constant function (φ_e(n) = Part.some c)
- **Class F:** the "bad" function — total, non-constant, representable

### Section structure

For e ∈ Class ⊥: smn(e,x) ∈ Class ⊥ (⊥ curried is ⊥)
For e ∈ Class C_c: smn(e,x) ∈ Class C_c (const curried is const)
For e ∈ Class F: smn(e,x) ∈ Class C_{f(x)} where f = the function F computes on the first component

**The section image of Class F is a subset of the constant classes.** This is the sectional poverty: sections of the non-constant function are all constants. No section of any index produces a non-constant function.

### I_comp failure

h₀ = the function mapping some inputs to ⊥-class indices and others to F-class indices. A tracker k needs smn(k,x) to hit both ⊥ and F classes. But sections of any k are either all ⊥, all constant, or all constant (from F). No k produces both ⊥ and non-⊥ sections.

### I_rec

For qualifying h: h(smn(x,x)) is representable. The diagonal smn(x,x) lands in {⊥, constants} (since the diagonal of F-class indices produces constants). So h(smn(x,x)) is a function of x whose values are determined by the diagonal. Fixed points:
- If h maps some ⊥-class index to itself: trivial fixed point
- If h maps a C_c-class index to a C_c-class index: fixed point in that class
- The key: h is constrained by its diagonal values, and we design enough fixed-point witnesses

---

# 3. Workstreams

## C1 — Finite model autopsy (§0 above) ✓

## C2 — Infinite fixed-point reservoir

Design the fixed-point mechanism for the infinite model. The ⊥ trick handles h with h(⊥-index) = ⊥-index. For other h, we need:

- For each constant class C_c, an index e_c with φ_{e_c} ∈ C_c
- Enough indices that h mapping within constant classes always has a fixed point
- The diagonal range must cover enough of the constant classes

**Key insight:** If the diagonal range = all constant-class indices, then h(smn(x,x)) determines h on all constant classes. The only freedom is h on ⊥-class and F-class indices (which are off-diagonal). If we ensure these off-diagonal indices have fixed points available, I_rec holds.

## C3 — Separate extensional from sectional richness

Prove that the architecture in §2 is consistent:
- Sections of F-class indices are constants (by design)
- Sections of constant-class indices are constants (by smn_spec)
- Sections of ⊥-class indices are ⊥ (by smn_spec)
- Therefore ALL sections are ⊥ or constant
- But F is non-constant ⇒ F is not a section ⇒ section surjectivity fails

## C4 — Diagonal-range engineering

Design smn so that:
- smn(x,x) covers all constant-class indices (or enough of them)
- smn(x,x) does NOT cover F-class indices
- smn(x,x) does NOT cover ⊥-class indices (or covers exactly one)

This constrains the qualifying h and makes I_rec manageable.

## C5 — Failure-set verification

For the intended bad h₀ (mapping to a mix of ⊥ and F classes):
- Verify F_k = {x : smn(k,x) ≄ h₀(x)} is nonempty for all k
- Verify no uniform x₀ witnesses failure for all k
- Verify this is compatible with I_rec

---

# 4. Targets

## Target 1 — APS skeleton

Construct a concrete infinite APS with:
- φ, smn satisfying smn_spec
- Extensional classes: ⊥, C_c for c ∈ ℕ, and F
- Section image ⊆ {⊥} ∪ {C_c | c ∈ ℕ}
- ¬I_comp for a specific representable h₀

No I_rec yet. Just get the geometry right.

## Target 2 — I_rec for constant h

Prove I_rec holds for h = const_c (all c). This is the easiest case and tests whether the fixed-point reservoir works.

## Target 3 — I_rec for all qualifying h

Prove I_rec holds for ALL qualifying h. This is the hard part. It requires:
- Analyzing which h qualify (have representable diagonal)
- Showing each has a fixed point
- The analysis depends on the diagonal range and the structure of φ

## Target 4 — Full separation theorem

Assemble: I_rec ∧ ¬I_comp.

---

# 5. The concrete model (first attempt)

## φ definition

```
φ_0(n) = Part.none                          -- ⊥
φ_{2*c+1}(n) = Part.some c                  -- constant c (odd indices)
φ_{2*c+2}(n) = Part.some (unpair n).1       -- fst (even indices ≥ 2)
```

Wait — this gives infinitely many copies of fst. That's too rich.

**Revised:** Only ONE non-constant function.

```
φ_0(n) = Part.none                          -- ⊥
φ_1(n) = Part.some (unpair n).1             -- fst (THE non-constant function)
φ_{c+2}(n) = Part.some c                    -- constant c (indices 2,3,4,...)
```

## smn definition

smn_spec requires φ(smn(e,x))(n) = φ_e(⟨x,n⟩).

- smn(0, x) = 0: φ_0(n) = ⊥ = φ_0(⟨x,n⟩). ✓
- smn(1, x) = x+2: φ_{x+2}(n) = Part.some x. φ_1(⟨x,n⟩) = Part.some (unpair(⟨x,n⟩)).1 = Part.some x. ✓
- smn(c+2, x) = c+2: φ_{c+2}(n) = Part.some c. φ_{c+2}(⟨x,n⟩) = Part.some c. ✓

## Diagonal

smn(0,0) = 0, smn(1,1) = 3, smn(2,2) = 2, smn(3,3) = 3, smn(4,4) = 4, ...
smn(c+2, c+2) = c+2 for c ≥ 0.

Range of smn(x,x): {0} ∪ {2, 3, 4, 5, ...} = ℕ \ {1}.

**Index 1 (fst) is NOT in the diagonal range.** This is the gap.

## Representability

- const_c is representable: index c+2, φ_{c+2}(n) = Part.some c. ✓
- fst is representable: index 1, φ_1(n) = Part.some (unpair n).1. ✓

## I_comp failure

h₀ = fst (as a function ℕ → ℕ, mapping n to (unpair n).1). Wait — h₀ should be a function ℕ → ℕ where we need a tracker. Let me reconsider.

I_comp says: for representable h : ℕ → ℕ, ∃ k, ∀ x n, φ_k(⟨x,n⟩) = φ_{h(x)}(n).

Take h = id (identity). Is id representable? We need ∃ e, ∀ n, φ_e(n) = Part.some n. φ_0 = ⊥, φ_1(n) = (unpair n).1, φ_{c+2}(n) = c. None of these equal Part.some n. So id is NOT representable.

Take h(x) = 0 for all x (constant 0). Representable: index 2 (φ_2(n) = 0). Tracker: need k with φ_k(⟨x,n⟩) = φ_0(n) = ⊥ for all x,n. k=0 works: φ_0(⟨x,n⟩) = ⊥. ✓

Take h(x) = x+2 (maps x to the index for const_x). Is this representable? Need e with φ_e(n) = Part.some(n+2). φ_1(n) = (unpair n).1 ≠ n+2 in general. Not representable.

What IS representable? h is representable iff ∃ e, ∀ n, φ_e(n) = Part.some(h(n)).
- φ_0: not total, so no h
- φ_1(n) = (unpair n).1: h(n) = (unpair n).1 = fst. So fst is representable.
- φ_{c+2}(n) = c: h(n) = c (constant). So const_c is representable.

**The representable functions are: fst and const_c for each c.**

I_comp for h = fst: need k with φ_k(⟨x,n⟩) = φ_{fst(x)}(n) = φ_{(unpair x).1}(n).

Now (unpair x).1 can be anything. If (unpair x).1 = 0: φ_0(n) = ⊥. If (unpair x).1 = 1: φ_1(n) = (unpair n).1. If (unpair x).1 = c+2: φ_{c+2}(n) = c.

So the tracker needs:
- φ_k(⟨⟨0,y⟩, n⟩) = ⊥ for all y,n (when fst(x) = 0, i.e., x = ⟨0,y⟩)
- φ_k(⟨⟨1,y⟩, n⟩) = (unpair n).1 for all y,n (when fst(x) = 1)
- φ_k(⟨⟨c+2,y⟩, n⟩) = c for all y,n (when fst(x) = c+2)

For k=0: φ_0 = ⊥ everywhere. Fails at ⟨⟨c+2,y⟩, n⟩ where we need c.
For k=1: φ_1(m) = (unpair m).1. φ_1(⟨⟨0,y⟩, n⟩) = (unpair(⟨⟨0,y⟩, n⟩)).1 = ⟨0,y⟩ ≠ ⊥. Actually φ_1 is total, so it returns Part.some(⟨0,y⟩), but we need Part.none. Fails.
For k=c+2: φ_{c+2} = const c. Fails for inputs where we need a different constant.

**No k works. I_comp fails for h = fst.** ✓

## I_rec

Qualifying h: h with representable fun x => h(smn(x,x)).

smn(x,x): smn(0,0)=0, smn(1,1)=3, smn(c+2,c+2)=c+2.
So smn(x,x) = 0 when x=0, and smn(x,x) = x when x ≥ 2, and smn(1,1) = 3.

Range = {0, 2, 3, 4, 5, ...} = ℕ \ {1}.

h(smn(x,x)) = h(0) when x=0, h(3) when x=1, h(x) when x ≥ 2.

So fun x => h(smn(x,x)) = the function that maps 0 ↦ h(0), 1 ↦ h(3), x ↦ h(x) for x ≥ 2.

This is representable iff it equals fst or some const_c.

**Case: fun x => h(smn(x,x)) = const_c.** Then h(0) = c, h(3) = c, h(x) = c for x ≥ 2. So h is constant c on {0} ∪ {2,3,4,...} = ℕ \ {1}. h(1) is free.

Fixed point needed: e with φ_e ≃ φ_{h(e)}.
- If e = 0: φ_0 = ⊥. h(0) = c. φ_{h(0)} = φ_c. Need ⊥ = φ_c. True iff c = 0 (φ_0 = ⊥). So if c = 0: e=0 works.
- If c ≠ 0: e=0 doesn't work. Try e = c+2: φ_{c+2} = const_c. h(c+2) = c (since c+2 ≥ 2). φ_{h(c+2)} = φ_c. Need const_c = φ_c.
  - If c = 0: φ_0 = ⊥ ≠ const_0. Doesn't work. But c=0 was handled above.
  - If c = 1: φ_1 = fst ≠ const_1. Doesn't work!
  - If c ≥ 2: φ_c = φ_{c} = const_{c-2} (since c = (c-2)+2). Need const_c = const_{c-2}. This requires c = c-2. False!

**PROBLEM.** For h with h(smn(x,x)) = const_1 (so h is constant 1 on ℕ\{1}, h(1) free):

We need e with φ_e ≃ φ_{h(e)}.
- h(e) = 1 for e ≠ 1. φ_{h(e)} = φ_1 = fst.
- Need φ_e = fst. The only index with φ_e = fst is e = 1.
- h(1) is free. If h(1) = 1: φ_{h(1)} = φ_1 = fst = φ_1. Fixed point at e=1! ✓
- If h(1) ≠ 1: h(1) = c ≠ 1. φ_{h(1)} = φ_c. Need φ_1 = φ_c, i.e., fst = φ_c. Only c=1 gives fst. Contradiction.

So for h with h(smn(x,x)) = const_1 and h(1) ≠ 1: NO fixed point exists!

**Is this h qualifying?** h(smn(x,x)) = const_1 is representable (index 3, φ_3 = const_1). And h(1) can be anything. So h(1) = 0 gives a qualifying h with no fixed point. **I_rec FAILS.**

## The problem

Index 1 (fst) is the unique representative of its extensional class, and it's off the diagonal. Any h that maps 1 away from {1} and maps everything else to 1 has no fixed point.

## The fix

We need MORE indices computing fst. If indices 1 and some other index both compute fst, and the other index IS on the diagonal, then h mapping 1 away still has a fixed point at the other index.

**Revised model:** Add a second fst index on the diagonal.

smn(1,1) = 3 (const_1). But we need an index e with φ_e = fst AND e ∈ range(smn(x,x)).

smn(x,x) = x for x ≥ 2. So if we make φ_e = fst for some e ≥ 2, then e is on the diagonal.

But φ_{c+2} = const_c. So no e ≥ 2 computes fst in our current scheme.

**We need to modify φ.** Let's reserve another index for fst.

---

# 6. Revised model (second attempt)

```
φ_0(n) = Part.none                          -- ⊥
φ_1(n) = Part.some (unpair n).1             -- fst (copy 1)
φ_2(n) = Part.some (unpair n).1             -- fst (copy 2, on diagonal)
φ_{c+3}(n) = Part.some c                    -- constant c
```

smn:
- smn(0, x) = 0
- smn(1, x) = x+3 (const_x)
- smn(2, x) = x+3 (const_x) — same as smn(1,x) since φ_1 = φ_2
- smn(c+3, x) = c+3 (const stays const)

Diagonal: smn(0,0)=0, smn(1,1)=4, smn(2,2)=5, smn(c+3,c+3)=c+3.
Range = {0, 3, 4, 5, ...} = ℕ \ {1, 2}.

**Still two gaps: indices 1 and 2 (both fst) are off-diagonal.**

For h with h(smn(x,x)) = const_1 and h(1) ≠ 1 and h(2) ≠ 1 and h(2) ≠ 2: no fixed point.

Adding more fst copies doesn't help if they're all off-diagonal.

**The core problem:** smn(e,e) for e computing fst gives const_e (the e-section of fst is const_e). So NO fst index is ever on the diagonal. This is structural, not an accident of our encoding.

## The structural theorem

For any APS and any index e with φ_e = fst (i.e., φ_e(n) = Part.some((unpair n).1)):

smn(e,e) computes: n ↦ φ_e(⟨e,n⟩) = (unpair(⟨e,n⟩)).1 = e.

So φ(smn(e,e)) = const_e. Therefore smn(e,e) ≠ e (extensionally) unless e is a constant function, which fst is not.

**No fst index is a diagonal fixed point.** The diagonal always "collapses" fst to a constant.

## Implication for I_rec

Any qualifying h that maps ALL fst indices away from fst indices will lack a fixed point — UNLESS there are infinitely many fst indices and the diagonal constraint forces h to preserve at least one.

**The question:** Can we have infinitely many fst indices, with the diagonal range covering all but finitely many of them, so that h is forced (by the diagonal constraint) to map at least one fst index to a fst index?

If the diagonal range = ℕ \ {finite set of fst indices}, and h is constant on the diagonal range, then h is determined on all but finitely many indices. The finite set of fst indices is where h is free. If there are k fst indices off-diagonal, h has k free values. For I_rec, we need: for every choice of these k values, a fixed point exists.

If k = 1 (one fst index off-diagonal): h(fst_idx) is free. If h(fst_idx) is a fst index, fixed point exists. If h(fst_idx) is not a fst index, we need another fixed point. The other indices are ⊥ or constants. h maps them according to the diagonal constraint. A fixed point among constants: e with φ_e = const_c and h(e) has φ_{h(e)} = const_c. This works if h(e) is in the same constant class as e.

**This is getting concrete enough to formalize. Let me build it.**

---

# 7. The model (third attempt, designed to work)

## Index structure

- Index 0: ⊥
- Index 1: fst (the ONE off-diagonal non-constant index)
- Index c+2: const_c for c ∈ ℕ

## φ

```
φ_0(n) = Part.none
φ_1(n) = Part.some (unpair n).1
φ_{c+2}(n) = Part.some c
```

## smn

```
smn(0, x) = 0
smn(1, x) = x + 2        -- const_x
smn(c+2, x) = c + 2      -- const stays const
```

## smn_spec verification

- smn(0,x): φ_0(n) = ⊥ = φ_0(⟨x,n⟩). ✓
- smn(1,x): φ_{x+2}(n) = Part.some x. φ_1(⟨x,n⟩) = Part.some (unpair(⟨x,n⟩)).1 = Part.some x. ✓
- smn(c+2,x): φ_{c+2}(n) = Part.some c = φ_{c+2}(⟨x,n⟩). ✓

## Diagonal

smn(0,0)=0, smn(1,1)=3, smn(c+2,c+2)=c+2.

Range of smn(x,x) = {0} ∪ {3} ∪ {2,3,4,...} = {0} ∪ {2,3,4,...} = ℕ \ {1}.

**Gap: {1}.** Index 1 (fst) is the sole off-diagonal index.

## Representable functions

- const_c: index c+2. ✓
- fst: index 1. ✓

## I_comp failure for h₀ = fst

Need k with φ_k(⟨x,n⟩) = φ_{fst(x)}(n) = φ_{(unpair x).1}(n).

When (unpair x).1 = 0: need φ_k(⟨x,n⟩) = ⊥.
When (unpair x).1 = 1: need φ_k(⟨x,n⟩) = (unpair n).1.
When (unpair x).1 = c+2: need φ_k(⟨x,n⟩) = c.

k=0: all ⊥. Fails when (unpair x).1 ≥ 2.
k=1: fst. φ_1(⟨x,n⟩) = (unpair(⟨x,n⟩)).1 = x. Need x = ⊥ when (unpair x).1 = 0. But x is a natural, not ⊥. Fails.
k=c+2: const_c. Fails when different constants needed.

**I_comp fails.** ✓

## I_rec analysis

Qualifying h: fun x => h(smn(x,x)) is representable (= fst or const_c).

smn(x,x) = 0 for x=0, 3 for x=1, x for x ≥ 2.

fun x => h(smn(x,x)) = [h(0), h(3), h(2), h(3), h(4), h(5), ...]

**Case A: fun x => h(smn(x,x)) = const_c.**
h(0) = c, h(3) = c, h(x) = c for x ≥ 2. So h = const_c on ℕ \ {1}. h(1) is free.

Fixed point: need e with φ_e ≃ φ_{h(e)}.

Sub-case c = 0: h = const_0 on ℕ\{1}. h(e) = 0 for e ≠ 1. φ_{h(e)} = φ_0 = ⊥.
  - e=0: φ_0 = ⊥ = φ_{h(0)} = φ_0 = ⊥. ✓ Fixed point!

Sub-case c = 1: h = const_1 on ℕ\{1}. h(e) = 1 for e ≠ 1. φ_{h(e)} = φ_1 = fst.
  - Need e with φ_e = fst. Only e=1. h(1) is free.
  - If h(1) = 1: φ_{h(1)} = φ_1 = fst = φ_1. Fixed point at e=1. ✓
  - If h(1) ≠ 1: φ_{h(1)} ≠ fst (since only index 1 computes fst). No fixed point. ✗

**I_rec FAILS for h with h = const_1 on ℕ\{1} and h(1) = 0.**

## The fix: make index 1 have multiple extensional copies

If we add index 1' also computing fst, and 1' is on the diagonal, then h(1') is determined by the diagonal constraint. If h(1') = 1 or h(1') = 1', we get a fixed point.

But we showed above: NO fst index can be on the diagonal (the diagonal collapses fst to a constant).

## Alternative fix: use partiality

What if index 1 computes a PARTIAL non-constant function? One that is undefined on some inputs? Then the diagonal smn(1,1) computes the 1-section, which might also be partial. If the 1-section happens to be extensionally equal to φ_1 itself...

smn(1,1) computes n ↦ φ_1(⟨1,n⟩). If φ_1 is designed so that φ_1(⟨1,n⟩) = φ_1(n) for all n, then smn(1,1) ≃ 1. That would put 1 on the diagonal!

**Condition:** φ_1(⟨1,n⟩) = φ_1(n) for all n. This means φ_1 is a "1-fixed-point" — its 1-section equals itself.

Can we design such a φ_1? Yes! Define φ_1 so that it only "looks at" the iterated second component of its input. For example:

φ_1(n) = Part.some (last_snd n)

where last_snd repeatedly takes the second component of unpair until reaching 0.

Actually, simpler: define φ_1(n) = Part.some (f n) where f(⟨1,n⟩) = f(n) for all n. This means f is invariant under prepending 1. A function with this property: f(n) = 0 if the "leftmost leaf" of the pair tree of n is 0, and f(n) = 1 otherwise. But this is getting complicated.

**Simplest approach:** φ_1(n) = Part.none for n ∉ {⟨1,m⟩ | m}, and φ_1(⟨1,n⟩) = Part.some (something depending on n). Then φ_1 is partial, and smn(1,1) computes n ↦ φ_1(⟨1,n⟩) = Part.some(something). The key: smn(1,1) is total on its domain while φ_1 is partial. They're NOT extensionally equal.

Hmm. Let me try yet another approach.

**What if φ_1 is total and satisfies φ_1(⟨1,n⟩) = φ_1(n)?**

Define φ_1 by: φ_1(n) = Part.some (g n) where g(⟨1,n⟩) = g(n) and g(⟨0,n⟩) = 0 and g(⟨c+2,n⟩) = c for all n.

Then g(n) depends on (unpair n).1: if it's 0, return 0; if it's 1, recurse on (unpair n).2; if it's c+2, return c.

g(⟨1, ⟨1, ⟨0, n⟩⟩⟩) = g(⟨1, ⟨0, n⟩⟩) = g(⟨0, n⟩) = 0.
g(⟨1, ⟨3, n⟩⟩) = g(⟨3, n⟩) = 1.

This g is well-defined (the recursion terminates because unpair strictly decreases... actually, it doesn't necessarily). In Lean's Nat.pair, unpair(⟨a,b⟩).2 = b, and for the recursion g(⟨1,n⟩) = g(n), we need n < ⟨1,n⟩. Since pair(1,n) = ... let me check.

Nat.pair 1 0 = 2, Nat.pair 1 1 = 4, Nat.pair 1 2 = 8. So pair(1,n) > n for n ≥ 0. Good — the recursion g(⟨1,n⟩) = g(n) terminates because n < ⟨1,n⟩.

But defining this in Lean requires well-founded recursion. Let me use a simpler characterization.

**g(n) = (unpair^k(n)).1 where k is the number of leading 1s in the pair tree.**

Or even simpler: g(n) = the first non-1 value in the sequence n, (unpair n).2, (unpair(unpair n).2).2, ...

Actually, for the countermodel we don't need g to be computable in any classical sense. We just need it to be a well-defined total function ℕ → ℕ satisfying g(pair(1,n)) = g(n).

**Definition:** g(n) = if (unpair n).1 = 1 then g((unpair n).2) else (unpair n).1.

This terminates because (unpair n).2 < n when (unpair n).1 ≥ 1 (in Lean's pairing, pair(a,b) > b when a ≥ 1).

Wait: pair(1, 0) = 2. unpair(2) = (1, 0). So g(2) = g(0). unpair(0) = (0,0). g(0) = 0. So g(2) = 0.
pair(1, 2) = 8. g(8) = g(2) = 0.
pair(3, 5) = some number. g(that) = 3.

This g is well-defined and satisfies:
- g(pair(0, n)) = 0
- g(pair(1, n)) = g(n)
- g(pair(c+2, n)) = c

And g is total.

**Now:** φ_1(n) = Part.some(g(n)). smn(1,1) computes n ↦ φ_1(pair(1,n)) = Part.some(g(pair(1,n))) = Part.some(g(n)) = φ_1(n).

**So smn(1,1) ≃ 1!** Index 1 IS on the diagonal!

**And g is non-constant:** g(0) = 0, g(pair(2,0)) = g(pair(2,0)). pair(2,0) = 3. g(3) = (unpair 3).1. unpair(3) = (0,2) in Lean? Let me check: pair(0,0)=0, pair(0,1)=1, pair(1,0)=2, pair(0,2)=3. So unpair(3) = (0,2). g(3) = 0.

Hmm, g(pair(2,0)) where pair(2,0) = ... pair(2,0) = 2 + 0 + (2+0)*(2+0+1)/2... Actually in Lean, Nat.pair a b = if a < b then b*b + a else a*a + a + b. pair(2,0) = 4 + 2 + 0 = 6. unpair(6) = (2,0). g(6) = 2. And g(0) = 0. So g is non-constant. ✓

**This is the model.** Let me formalize it.

---

# 8. The working model

## φ

```
g(n) = if (unpair n).1 = 1 then g((unpair n).2) else (unpair n).1
-- well-founded: (unpair n).2 < n when (unpair n).1 ≥ 1

φ_0(n) = Part.none                    -- ⊥
φ_1(n) = Part.some (g n)              -- non-constant, self-sectioning at 1
φ_{c+2}(n) = Part.some c              -- constant c
```

## smn

```
smn(0, x) = 0
smn(1, x) = ?                         -- need φ(smn(1,x))(n) = φ_1(pair(x,n)) = g(pair(x,n))
smn(c+2, x) = c+2
```

For smn(1,x): need index e with φ_e(n) = Part.some(g(pair(x,n))).

g(pair(x,n)):
- If x = 0: g(pair(0,n)) = 0. So smn(1,0) should be index for const_0 = index 2.
- If x = 1: g(pair(1,n)) = g(n). So smn(1,1) should be index 1 (itself!).
- If x = c+2: g(pair(c+2,n)) = c. So smn(1,c+2) should be index for const_c = index c+2.

**smn(1, x) = if x = 1 then 1 else (if x = 0 then 2 else x)**

Simplify: smn(1, 0) = 2, smn(1, 1) = 1, smn(1, x) = x for x ≥ 2.

Check: smn(1,x) = x for x ≥ 2, smn(1,1) = 1, smn(1,0) = 2.

Even simpler: smn(1, x) = if x = 0 then 2 else x.

Check smn_spec for e=1:
- x=0: φ(smn(1,0))(n) = φ_2(n) = 0. φ_1(pair(0,n)) = g(pair(0,n)) = 0. ✓
- x=1: φ(smn(1,1))(n) = φ_1(n) = g(n). φ_1(pair(1,n)) = g(pair(1,n)) = g(n). ✓
- x=c+2: φ(smn(1,c+2))(n) = φ_{c+2}(n) = c. φ_1(pair(c+2,n)) = g(pair(c+2,n)) = c. ✓

**smn_spec holds!**

## Diagonal

smn(0,0) = 0. smn(1,1) = 1. smn(c+2,c+2) = c+2.

**Range of smn(x,x) = ℕ.** The diagonal is SURJECTIVE!

## I_rec analysis

Since smn(x,x) = x for x ≥ 2, and smn(0,0) = 0, smn(1,1) = 1:

Actually smn(x,x) = x for ALL x:
- x=0: smn(0,0) = 0. ✓
- x=1: smn(1,1) = 1. ✓
- x≥2: smn(x,x) = x (since x ≥ 2, smn(c+2, c+2) = c+2 where c = x-2). ✓

**smn(x,x) = x for all x!** The diagonal is the identity!

So fun x => h(smn(x,x)) = h itself. The representability condition becomes: h itself is representable.

**I_rec says: for every representable h, ∃ e, φ_e ≃ φ_{h(e)}.**

The representable functions are: const_c (for all c) and g (via index 1).

### I_rec for h = const_c

h(e) = c for all e. Need e with φ_e ≃ φ_c.
- c = 0: φ_0 = ⊥. Need e with φ_e = ⊥. e=0. ✓
- c = 1: φ_1 = g. Need e with φ_e = g. e=1. ✓
- c = d+2: φ_{d+2} = const_d. Need e with φ_e = const_d. e=d+2. ✓

**I_rec holds for all constant h.** ✓

### I_rec for h = g

h = g. Need e with φ_e ≃ φ_{g(e)}.

- e=0: g(0) = 0. φ_0 = ⊥. φ_{g(0)} = φ_0 = ⊥. φ_0 ≃ φ_0. ✓ Fixed point!

**I_rec holds for h = g.** ✓

### I_rec complete

The only representable functions are const_c and g. We've shown fixed points exist for all of them.

**I_rec holds.** ✓

## I_comp failure

h₀ = g (representable via index 1). Need k with ∀ x n, φ_k(pair(x,n)) = φ_{g(x)}(n).

g(x) values:
- g(0) = 0 → φ_0 = ⊥
- g(1) = g(1). What is g(1)? unpair(1) = (0,1). g(1) = 0 (since (unpair 1).1 = 0 ≠ 1).
  So g(1) = 0 → φ_0 = ⊥
- g(2) = (unpair 2).1 = 1 (since unpair(2) = (1,0)). Since 1 = 1, g(2) = g(0) = 0.
  Wait: g(2): unpair(2) = (1,0). (unpair 2).1 = 1. Since 1 = 1, g(2) = g((unpair 2).2) = g(0) = 0.
  So g(2) = 0 → φ_0 = ⊥

Hmm, let me compute more values of g.

g(0): unpair(0) = (0,0). fst = 0 ≠ 1. g(0) = 0.
g(1): unpair(1) = (0,1). fst = 0 ≠ 1. g(1) = 0.
g(2): unpair(2) = (1,0). fst = 1. g(2) = g(0) = 0.
g(3): unpair(3) = (0,2). fst = 0. g(3) = 0.
g(4): unpair(4) = (1,1). fst = 1. g(4) = g(1) = 0.
g(5): unpair(5) = (0,3). fst = 0. g(5) = 0.
g(6): unpair(6) = (2,0). fst = 2 ≠ 1. g(6) = 2.

**g(6) = 2!** So g is non-constant (g(0)=0, g(6)=2).

g(x) for the tracker: need φ_k(pair(x,n)) = φ_{g(x)}(n).

For x=0: g(0)=0. φ_0(n) = ⊥. Need φ_k(pair(0,n)) = ⊥.
For x=6: g(6)=2. φ_2(n) = 0. Need φ_k(pair(6,n)) = Part.some 0.

So k must be undefined at pair(0,n) and defined (= 0) at pair(6,n).

k=0: ⊥ everywhere. Fails at pair(6,n).
k=1: φ_1(pair(0,n)) = g(pair(0,n)) = 0 (defined, not ⊥). Fails.
k=c+2: const_c. φ_{c+2}(pair(0,n)) = c (defined, not ⊥). Fails.

**No k works. I_comp fails for h = g.** ✓

## Summary

**The model works!**

- φ_0 = ⊥, φ_1 = g (non-constant, self-sectioning), φ_{c+2} = const_c
- smn(0,x) = 0, smn(1,x) = if x=0 then 2 else x, smn(c+2,x) = c+2
- smn_spec: ✓
- Diagonal: smn(x,x) = x (identity)
- Representable functions: const_c and g
- I_rec: ✓ (const_c has fixed point c+2 or 0 or 1; g has fixed point 0)
- I_comp: ✗ (g requires mixing ⊥ and defined values; no index can do this)

**This is the countermodel.**
