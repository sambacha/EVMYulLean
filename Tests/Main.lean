import EvmYul.ArbOS.Abi
open EvmYul ABI
def sigs : List String := [
  "arbBlockNumber()", "arbBlockHash(uint256)", "arbChainID()", "arbOSVersion()",
  "getStorageGasAvailable()", "isTopLevelCall()",
  "mapL1SenderContractAddressToL2Alias(address,address)",
  "wasMyCallersAddressAliased()", "myCallersAddressWithoutAliasing()",
  "withdrawEth(address)", "sendTxToL1(address,bytes)",
  "getPricesInWei()", "getL1BaseFeeEstimate()", "getMinimumGasPrice()",
  "getCurrentTxL1GasFees()", "getGasAccountingParams()", "getPricesInArbGas()",
  "getL1GasPriceEstimate()", "getPricesInWeiWithAggregator(address)",
  "getArbOSVersion()"
]
def main : IO Unit := do
  for s in sigs do
    IO.println s!"{s} => 0x{Nat.toHex (methodId s).toNat}"
