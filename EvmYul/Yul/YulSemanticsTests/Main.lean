module

public import EvmYul.Yul.Interpreter
public import EvmYul.Yul.YulNotation
public import EvmYul.Yul.YulSemanticsTests.StorageContracts
public import EvmYul.Yul.YulSemanticsTests.CallerContracts

/-!
# Entry point of `lake exe yulSemanticsTests`

Runs the Yul storage and caller contracts through the interpreter and checks the resulting
storage. It needs the FFI primitives, so it runs as an executable, not with `#eval`.
-/

@[expose] public section

namespace EvmYul

namespace Yul

open Ast SizeLemmas

def callerAddressUInt256 : UInt256 := ⟨1⟩
def storageAddressUInt256 : UInt256 := ⟨2⟩
def caller2AddressUInt256 : UInt256 := ⟨3⟩
def storage2AddressUInt256 : UInt256 := ⟨4⟩
def callerAddress := AccountAddress.ofUInt256 callerAddressUInt256
def storageAddress := AccountAddress.ofUInt256 storageAddressUInt256
def caller2Address := AccountAddress.ofUInt256 caller2AddressUInt256
def storage2Address := AccountAddress.ofUInt256 storage2AddressUInt256


def stateEg₁ : Yul.State :=
  let storageAccount : Account .Yul :=
    { code := storageCode
    , balance := ⟨1000⟩
    , nonce := ⟨0⟩ 
    , storage := Std.TreeMap.ofList [(⟨0⟩, ⟨21⟩)] compare
    , tstorage := ∅
    }
  let callerAccount : Account .Yul :=
    { code := callerCode
    , balance := ⟨1000⟩
    , nonce := ⟨0⟩ 
    , storage := ∅
    , tstorage := ∅
    }
    
    let caller2Account : Account .Yul :=
    { code := caller2Code
    , balance := ⟨1000⟩
    , nonce := ⟨0⟩ 
    , storage := ∅
    , tstorage := ∅
    }
 
let storage2Account : Account .Yul :=
    { code := storage2Code
    , balance := ⟨1000⟩
    , nonce := ⟨0⟩ 
    , storage := ∅
    , tstorage := ∅
    }
    
  let accountMap : AccountMap .Yul := Std.TreeMap.insert ∅ storageAddress storageAccount
                                      |>.insert callerAddress callerAccount
                                      |>.insert caller2Address caller2Account
                                      |>.insert storage2Address storage2Account
  let sharedState : SharedState .Yul :=
    { accountMap := accountMap
    , σ₀ := ∅
    , totalGasUsedInBlock := 0
    , transactionReceipts := #[]
    , substate := Inhabited.default
    , executionEnv := 
        { calldata := ByteArray.mk #[]
        , code := Inhabited.default
        , codeOwner := callerAddress
        , source := Inhabited.default
        , weiValue := ⟨0⟩
        , sender := Inhabited.default
        , gasPrice := 0
        , header := (Inhabited.default : BlockHeader)
        , depth := 0
        , perm := true
        , blobVersionedHashes := []
        }
    , blocks := ∅
    , genesisBlockHeader := Inhabited.default
    , createdAccounts := ∅
    , gasAvailable := ⟨0⟩
    , activeWords := ⟨0⟩
    , memory := ByteArray.mk #[]
    , returnData := ByteArray.mk #[]
    , H_return := ByteArray.mk #[]
    }
  Yul.State.Ok sharedState ∅
    
def test₁ :=
  let expr : Expr := .Call (Sum.inr "fun_testStoreAndRetrieveExternal") [.Lit ⟨42⟩]
  match (exec 99 (.ExprStmtCall expr) .none stateEg₁) with
  | .error e => repr e
  | .ok s => s!"{s.toSharedState.accountMap.toList.map (fun (a : AccountAddress × Account .Yul) => repr a.1 ++ " " ++ repr a.2.storage.toList)}"

def stateEg₂ : Yul.State :=
  Yul.State.Ok {stateEg₁.toSharedState with executionEnv := {stateEg₁.toSharedState.executionEnv with codeOwner := caller2Address, perm := true}} Inhabited.default
  
def test₂ :=
  let expr : Expr := .Call (Sum.inr "fun_testStaticRetrieve") []
  match (exec 99 (.ExprStmtCall expr) .none stateEg₂) with
  | .error e => repr e
  | .ok s => s!"{s.toSharedState.accountMap.toList.map (fun (a : AccountAddress × Account .Yul) => repr a.1 ++ " " ++ repr a.2.storage.toList)}"

def test₃ :=
  let expr : Expr := .Call (Sum.inr "fun_testStaticStore") [.Lit ⟨42⟩]
  match (exec 99 (.ExprStmtCall expr) .none stateEg₂) with
  | .error e => repr e
  | .ok s => s!"{s.toSharedState.accountMap.toList.map (fun (a : AccountAddress × Account .Yul) => repr a.1 ++ " " ++ repr a.2.storage.toList)}"

def stateEg₄ : Yul.State :=
  Yul.State.Ok {stateEg₁.toSharedState with executionEnv := {stateEg₁.toSharedState.executionEnv with codeOwner := storageAddress, perm := true}} Inhabited.default


def test₄ :=
  let expr : Expr := .Call (Sum.inr "fun_storageDelegateCallTest") []
  match (exec 99 (.ExprStmtCall expr) .none stateEg₄) with
  | .error e => repr e
  | .ok s => s!"{s.toSharedState.accountMap.toList.map (fun (a : AccountAddress × Account .Yul) => repr a.1 ++ " " ++ repr a.2.storage.toList)}"

def test₅ :=
  let expr : Expr := .Call (Sum.inr "fun_storageCallCodeTest") []
  match (exec 99 (.ExprStmtCall expr) .none stateEg₄) with
  | .error e => repr e
  | .ok s => s!"{s.toSharedState.accountMap.toList.map (fun (a : AccountAddress × Account .Yul) => repr a.1 ++ " " ++ repr a.2.storage.toList)}"


end Yul

end EvmYul

open EvmYul.Yul

-- Run this test via `lake exe yulSemanticsTests`.
-- `#eval` cannot run the test because it uses the foreign function interface for `ByteArray.zeroes`.
def main : IO UInt32 := do
  let cases : List (String × String × String) :=
    [("test₁", s!"{test₁}", "[1 [(0, 42)], 2 [(0, 42)], 3 [], 4 []]"),
     ("test₂", s!"{test₂}", "[1 [], 2 [(0, 21)], 3 [(0, 21)], 4 []]"),
     ("test₃", s!"{test₃}", "StaticModeViolation"),
     ("test₄", s!"{test₄}", "[1 [], 2 [(0, 5)], 3 [], 4 []]"),
     ("test₅", s!"{test₅}", "[1 [], 2 [(0, 5)], 3 [], 4 []]")]
  let mut failures := 0
  for (name, got, expected) in cases do
    let ok := got == expected
    unless ok do failures := failures + 1
    IO.println (s!"{name}: {got} -- " ++ (if ok then "Success" else s!"Failure (expected {expected})"))
  -- a failing case makes the executable fail, so CI and scripts see it (it used to exit 0)
  return if failures == 0 then 0 else 1
