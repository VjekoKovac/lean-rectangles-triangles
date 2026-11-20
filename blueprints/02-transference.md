# Theorem 1.3 · Euclidean-to-periodic transference

For every integer $d\ge1$ and every real $N\ge1$, the periodic Stein constant at $N$ is at most the Euclidean Stein constant at $N+1$. The same comparison holds for the Mizohata–Takeuchi (MT) constants. Both comparisons have coefficient one. This is Theorem 1.3, page 8, of Bennett, Kovač, Nakamura, and Oliveira, [arXiv:2606.30178v1](https://arxiv.org/abs/2606.30178v1). Its proof is in §3.1.

## What the constants quantify over

| Input | Periodic | Euclidean |
| --- | --- | --- |
| Data | Finitely supported complex coefficients on the integer lattice | Square-integrable complex Fourier profile, parametrizing square-integrable initial data by Plancherel |
| Frequency constraint | Every coordinate in $[-N,N]$ | Closed essential frequency support in $[-N-1,N+1]^d$ |
| Weighted energy | Integrate the squared solution times the weight over one spacetime period, with Haar probability measures | Integrate the same expression over all space and the time interval $[0,1]$ |
| Ray through a base point | Follow $x-2tk$ over one period for integer $k$ | Follow $x-2tv$ over all real times for real $v$ |
| Stein denominator | Sum over the frequency support of the squared modulus of each coefficient times the spatial ray supremum at its own velocity | Integrate the analogous quantity against Lebesgue measure in frequency space |
| MT denominator | Multiply the total coefficient energy by the supremum over all base points and frequencies in the actual support | Multiply the initial energy by the supremum over all base points and velocities in the essential closed support |

The common Fourier phase has a positive sign on both $x\cdot\xi$ and $t|\xi|^2$. Weights are nonnegative locally integrable functions. The code retains their pointwise representatives because changing a weight on a spacetime-null set can change its integral along an individual line. Both sharp constants are infima in the extended nonnegative reals. Section 3.2 of the paper gives a qualitative converse, outside the statement of Theorem 1.3.

## How to follow the proof in Lean

1. Fix an admissible finite Euclidean constant $C$, a coefficient family $a$, and a continuous nonnegative periodic weight $w$. Its spatially periodic lift, truncated to one time period, is a Euclidean weight. On each integer velocity its ray integral agrees with the original periodic ray. The maximum ray integral for a real velocity varies continuously by compactness of the base torus. See `liftedWeight_eligible`, `integer_ray_lift`, `lifted_eucXray_sup`, and `continuous_rayMax`.
2. Thicken each frequency $k$ by the same translated packet. The paper uses a smooth frequency bump. The Lean proof takes the indicator of $(0,r]^d$, with $0<r<1/2$. This bounded square-integrable packet is admissible as Euclidean initial frequency data. Each packet has squared mass $r^d$. The translates are disjoint, and their closed supports fit inside the enlarged box. See `profile_memLp`, `profile_in_box`, and `profile_enorm_sq`.
3. Tile Euclidean space by translates of a half-open unit cell. At each point $(x,t)$, express the physical translate $u(x+j,t)$ as the Fourier coefficient at $-j$ of the packet function on the auxiliary frequency torus. Apply its Parseval identity. This turns the sum over lattice translates into an integral of the squared shifted wave against the squared bump. See `lintegral_periodize`, `physical_packet_coefficient`, `physical_packet_hasSum`, and `packetLHS_cell`. The sign is explicit because the Fourier synthesis phase is positive. The Parseval input is David Loeffler's `UnitAddTorus.hasSum_sq_mFourierCoeff` in mathlib.
4. Rescale each small box to the unit box. Cancel its common, strictly positive finite mass $r^d$. Continuity of parameterized integrals on compact sets gives the left-hand limit `cellEnergy_continuous`. At radius zero, `perLHS_cell` and `sum_phase_eq_perWave` identify it with the periodic weighted energy.
5. For Stein, each translated frequency packet samples the ray maximum at its own center. The exact packet integral is `stein_profile_rhs`, and its normalized limit follows from `steinAverage_continuous`. For MT, `profile_mass` computes the total energy and `cost_le_mtEnvelope` bounds the support-wide supremum by the maximum over the closed packets. As $r$ tends to zero, that envelope tends to the maximum over the original finite support. The empty support is handled separately. Both limits enter `continuous_transfer`.
6. Convolve a weight with nonnegative unit-mass approximate identities on the spacetime torus. The weighted energy converges, and the spatial ray supremum at each integer velocity can only decrease. For an almost-everywhere measurable weight, first choose a measurable pointwise minorant equal to it almost everywhere. This preserves the numerator and permits the pointwise comparison of the ray denominators. See `Smoothing.perAdmissible_of_continuous`.
7. Take the infimum over admissible Euclidean constants. An infinite candidate is handled directly by the order relation. The final declaration is `RTS.quantitativeTransference` in `RTS/TransferenceProof.lean`.

The statement is frozen independently of these auxiliary definitions in the repository's `Challenge.lean`. The verification files report the status of the full solution and comparator run.
