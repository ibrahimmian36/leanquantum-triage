/- Second, independent inventory method: dump every declaration the compiled
ForMathlib modules actually contain, straight from the elaborated
environment — no regex involved.
Run from vendor/LeanQuantum:  lake env lean ../../inventory/DumpDecls.lean -/
import Quantumlib.ForMathlib.Data.BitVec.Basic
import Quantumlib.ForMathlib.Data.BitVec.Lemmas
import Quantumlib.ForMathlib.Data.Complex.Basic
import Quantumlib.ForMathlib.Data.Fin
import Quantumlib.ForMathlib.Data.Matrix.Basic
import Quantumlib.ForMathlib.Data.Matrix.Kron
import Quantumlib.ForMathlib.Data.Matrix.PowBitVec
import Quantumlib.ForMathlib.Data.Matrix.Unitary

open Lean in
run_meta do
  let env ← getEnv
  let mods := env.header.moduleNames
  let mdata := env.header.moduleData
  let auxMarkers := ["._", ".eq_", ".sizeOf_spec", ".noConfusion", ".casesOn",
                     ".rec", ".brecOn", ".below", ".ibelow", ".binductionOn",
                     ".induct", ".injEq", ".mk", ".proof_"]
  for (modName, mod) in mods.zip mdata do
    if modName.toString.startsWith "Quantumlib.ForMathlib" then
      for c in mod.constNames do
        let s := c.toString
        let isAux := auxMarkers.any (fun t => (s.splitOn t).length > 1)
        if !isAux then
          IO.println s!"{modName}\t{c}"
