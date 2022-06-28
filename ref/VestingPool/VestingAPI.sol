pragma ton-solidity >=0.61.0;
pragma AbiHeader expire;
pragma AbiHeader time;
pragma AbiHeader pubkey;
import "https://raw.githubusercontent.com/tonlabs/debots/main/Debot.sol";
import "DeBotInterfaces.sol";
import "./interfaces/IVestingService.sol";
import "./interfaces/IVestingPool.sol";
import "./interfaces/IVestingAPI.sol";
import "Modifiers.sol";
import "../Upgradable.sol";
import "../IMultisig.sol";

struct CreateReq {
    uint128 amount;
    uint8 cliffMonths;
    uint8 vestingMonths;
    address recipient;
    uint256[] claimers;
}

contract VestingAPI is Debot, Modifiers, Upgradable {
    bytes m_icon;
    address m_invoker;
    address m_service;
    address m_pool;
    address m_last;
    PoolInfo[] m_pools;
    optional(CreateReq) m_createReq;
    uint32 m_sbHandle;
    address m_wallet;
    address[] m_poolAddrs;

    /// @notice Returns Metadata about DeBot.
    function getDebotInfo() public functionID(0xDEB) override view returns(
        string name, string version, string publisher, string caption, string author,
        address support, string hello, string language, string dabi, bytes icon
    ) {
        name = "Vesting API";
        version = "0.3.0";
        publisher = "Ever Surf";
        caption = "Pooler";
        author = "Vesting API";
        support = address(0x606545c3b681489f2c217782e2da2399b0aed8640ccbcf9884f75648304dbc77);
        hello = "";
        language = "en";
        dabi = m_debotAbi.get();
        icon = m_icon;
    }

    function getRequiredInterfaces() public view override returns (uint256[] interfaces) {
        return [ UserInfo.ID, Sdk.ID ];
    }

    function setService(address addr) public onlyOwner accept {
        m_service = addr;
    }

    function start() public override {}

    //
    // API functions
    // 

    function invokeGetPools() public {
        m_invoker = msg.sender;
        m_last = address(0);
        delete m_pools;
        delete m_poolAddrs;
        _gethash(tvm.functionId(onGetHash));
    }

    function invokeCreatePool(
        uint128 amount,
        uint8 cliffMonths,
        uint8 vestingMonths,
        address recipient,
        uint256[] claimers
    ) public {
        m_invoker = msg.sender;
        CreateReq req;
        req.amount = amount;
        req.cliffMonths = cliffMonths;
        req.vestingMonths = vestingMonths;
        req.recipient = recipient;
        req.claimers = claimers;
        m_createReq = req;
        UserInfo.getSigningBox(tvm.functionId(setSigingBox));
        UserInfo.getAccount(tvm.functionId(createPool));
    }

    function invokePoolGet(address pool) public {
        m_invoker = msg.sender;
        delete m_pools;
        _getpool(pool, tvm.functionId(onGetPool));
        this.retPoolInfo();
    }

    function invokeClaim(address pool) public {
        m_invoker = msg.sender;
        m_pool = pool;
        delete m_pools;
        _getpool(pool, tvm.functionId(onGetPool));
        UserInfo.getSigningBox(tvm.functionId(setSigingBox));
        this.doClaim();
    }

    function invokeUnlock(address pool) public {
        m_invoker = msg.sender;
        m_pool = pool;
        UserInfo.getSigningBox(tvm.functionId(setSigingBox));
        UserInfo.getAccount(tvm.functionId(doUnlock));
    }

    // ------------------------------------------------------------------------
    function doUnlock(address value) public view {
        TvmCell body = tvm.encodeBody(IdbgPool.unlock);
        IMultisig(value).sendTransaction{
            time: 0, expire: 0, sign: true, pubkey: 0,
            signBoxHandle: m_sbHandle,
            callbackId: onClaimSuccess,
            onErrorId: onClaimError
        }(m_pool, 0.02 ton, true, 3, body).extMsg;
    }

    function doClaim() public view {
        IVestingPool(m_pool).claim{
            time: 0, expire: 0, sign: true, pubkey: 0,
            signBoxHandle: m_sbHandle,
            callbackId: onClaimSuccess,
            onErrorId: onClaimError
        }(m_pools[0].poolId).extMsg;
    }

    function onClaimSuccess() public view {
        IOnClaim(m_invoker).onClaim(VAPIStatus.Success);
    }

    function onClaimError(uint32 sdkError, uint32 exitCode) public view {
        Terminal.print(0, format("DBG: error sdk{} exit{}", sdkError, exitCode));
        IOnClaim(m_invoker).onClaim(VAPIStatus.Failed);
    }
    
    function setSigingBox(uint32 handle) public {
        m_sbHandle = handle;
    }

    function createPool(address value) public {
        m_wallet = value;
        CreateReq req = m_createReq.get();
        TvmCell body = tvm.encodeBody(IVestingService.createPool, 
            req.amount, req.cliffMonths, req.vestingMonths, req.recipient, req.claimers);
        IMultisig(value).sendTransaction{
            time: 0, expire: 0, sign: true, pubkey: 0,
            signBoxHandle: m_sbHandle,
            callbackId: onSuccess,
            onErrorId: onError
        }(m_service, req.amount + calcCreateGasFee(uint128(req.claimers.length)), true, 3, body).extMsg;
    }
    
    function onSuccess() public view {
        _oncreatepool(true);
    }

    function onError(uint32 sdkError, uint32 exitCode) public view {
        sdkError; exitCode;
        _oncreatepool(false);
    }

    function onGetPool(uint poolId, 
        address poolCreator,
        uint32 createdAt,
        address recipient,
        uint32 cliffEnd,
        uint32 vestingEnd,
        uint128 totalAmount,
        uint128 remainingAmount,
        uint128 unlockedAmount) public {
        m_pools.push(PoolInfo(address(0),
            poolId, poolCreator, createdAt, recipient, cliffEnd, vestingEnd,
            totalAmount, remainingAmount, unlockedAmount
        ));
    }
    function retPoolInfo() public view {
        IOnPoolInfo(m_invoker).onPoolInfo(m_pools[0]);
    }

    function onGetPools() public {
        for (uint i = 0; i < m_pools.length; i++) {
            m_pools[i].addr = m_poolAddrs[i];
        }
        IOnGetPools(m_invoker).onGetPools(m_pools);
    }

    function onGetHash(uint256 codeHash) public view {
        Sdk.getAccountsDataByHash(tvm.functionId(setPoolAccounts), codeHash, m_last);
    }

    function setPoolAccounts(AccData[] accounts) public {
        for (AccData acc: accounts) {
            m_poolAddrs.push(acc.id);
            _getpool(acc.id, tvm.functionId(AddPool));
        }
        this.onGetPools();
    }

    function AddPool(uint poolId, 
        address poolCreator,
        uint32 createdAt,
        address recipient,
        uint32 cliffEnd,
        uint32 vestingEnd,
        uint128 totalAmount,
        uint128 remainingAmount,
        uint128 unlockedAmount) public {
        m_pools.push(PoolInfo(address(0),
            poolId, poolCreator, createdAt, recipient, cliffEnd, vestingEnd,
            totalAmount, remainingAmount, unlockedAmount
        ));
    }

    function _getpool(address pool, uint32 callbackId) private pure {
        optional(uint256) none;
        IVestingPool(pool).get{
            time: 0, expire: 0, pubkey: none,
            callbackId: callbackId,
            onErrorId: 0
        }().extMsg;
    }

    function _gethash(uint32 callbackId) private view {
        optional(uint256) none;
        IVestingService(m_service).getPoolCodeHash{
            time: 0, expire: 0, pubkey: none,
            callbackId: callbackId,
            onErrorId: 0
        }().extMsg;
    }

    function _oncreatepool(bool status) public view {
        IOnCreatePool(m_invoker).onCreatePool(status);
    }

    /*
    function _decodePoolData(address pool, TvmCell data) private returns (PoolInfo) {
        TvmSlice s = data.toSlice();
        (
            , , ,
            uint id, 
            address creator, 
            uint32 createdAt,
            uint32 cliffEnd,
            uint32 vestingEnd,
            uint32 vestingFrom,
            uint128 totalAmount,
            uint128 remainingAmount
        ) = s.decode(
            uint256, uint64, bool, // pubkey, timestamp, ctor flag
            uint, address, uint32, uint32, uint32, uint32, uint128, uint128
        );
        s = s.loadRefAsSlice();
        (
            uint128 vestingAmount,
            address recipient,
            mapping(uint256 => bool) claimers
        ) = s.decode(uint128, address, mapping(uint256 => bool));

        return PoolInfo(pool, id, creator, createdAt, recipient, cliffEnd, 
            vestingEnd, totalAmount, remainingAmount, unlockedAmount
        )
    }
    */

    uint128 constant FEE_CLAIM = 0.1 ton;
    uint128 constant FEE_CREATE = 0.1 ton;
    uint128 constant CONSTRUCTOR_GAS = 0.1 ton;
    function calcCreateGasFee(uint128 count) private pure returns (uint128) {
        return CONSTRUCTOR_GAS + count * FEE_CLAIM + FEE_CREATE;
    }


    function onCodeUpgrade() internal override {
        tvm.resetStorage();
    }
}

