pragma ton-solidity >= 0.61.0;

enum VAPIStatus {
    Success,
    Failed
}

struct PoolInfo {
    address addr;
    uint poolId;
    address poolCreator;
    uint32 createdAt;
    address recipient;
    uint32 cliffEnd;
    uint32 vestingEnd;
    uint128 totalAmount;
    uint128 remainingAmount;
    uint128 unlockedAmount;
}

interface IOnCreatePool {
    function onCreatePool(bool status) external;
}

interface IOnPoolInfo {
    function onPoolInfo(PoolInfo pool) external;
}

interface IOnGetPools {
    function onGetPools(PoolInfo[] pools) external;
}

interface IOnClaim {
    function onClaim(VAPIStatus status) external;
}

contract VestingAPI_ABI is IOnCreatePool, IOnPoolInfo, IOnGetPools, IOnClaim {
    function onCreatePool(bool status) external override {}
    function onPoolInfo(PoolInfo pool) external override {}
    function onGetPools(PoolInfo[] pools) external override {}
    function onClaim(VAPIStatus status) external override {}
}