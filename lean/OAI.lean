-- Default package entry point: the public theorems and their axiom audit.
-- Theorem S / S′ (prime dividing |G| exactly once) and its corollaries.
import OAI.LinearAlgebra.CirculantHadamard.TheoremS.Main
import OAI.LinearAlgebra.CirculantHadamard.TheoremS.Sharp
import OAI.LinearAlgebra.CirculantHadamard.TheoremS.RDS
-- Ramified regime: Lemma A and Theorem C (m = q and m = q ^ e).
import OAI.LinearAlgebra.CirculantHadamard.RamifiedComparison.LemmaA
import OAI.LinearAlgebra.CirculantHadamard.RamifiedComparison.TheoremC
import OAI.LinearAlgebra.CirculantHadamard.RamifiedComparison.PrimePower
-- `#print axioms` guards.
import OAI.LinearAlgebra.CirculantHadamard.PrimeOnceAudit
