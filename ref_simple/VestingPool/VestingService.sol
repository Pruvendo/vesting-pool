pragma ton-solidity >=0.61.0;
pragma AbiHeader expire;
pragma AbiHeader time;
pragma AbiHeader pubkey;
import "./interfaces/IVestingService.sol";
import "VestingPool.sol";
import "Modifiers.sol";
// import "../Upgradable.sol";
contract VestingService is IVestingService, Modifiers 
{
    uint128 constant FEE_CLAIM = 0.1 ton;
    uint128 constant FEE_CREATE = 0.1 ton;
    uint128 constant CONSTRUCTOR_GAS = 0.1 ton;

    TvmCell m_poolCode;
    uint256 m_nextId;

    constructor(TvmCell poolImage) public onlyOwner accept {
        m_poolCode = poolImage.toSlice().loadRef();
        m_nextId = 1;
    }

    /// @notice Allows to create pool with cliff and vesting params
    /// @param amount Total amount of funds in Pool, in nanoevers
    /// @param cliffMonths Lock period before vesting starts, in months
    /// @param vestingMonths Total vesting period with step = 1 month, in months
    /// @param recipient Recipient address of pool funds
    /// @param claimers Array of public keys which allowed to request funds from pool.
    function createPool(
        uint128 amount,
        uint8 cliffMonths,
        uint8 vestingMonths,
        address recipient,
        uint256[] claimers
    ) external override contractOnly minValue(amount + calcCreateGasFee(uint128(claimers.length))){
        //require(msg.value >= amount + calcCreateGasFee(claimers.length), ERR_LOW_VALUE);
        mapping(uint256 => bool) claimersMap;
        for(uint256 pubkey: claimers) {
            claimersMap[pubkey] = true;
        }
        new VestingPool{
            value: 0,
            flag: 64,
            bounce: true,
            stateInit: buildPoolImage(msg.sender, m_nextId)
        }(amount, cliffMonths, vestingMonths, recipient, claimersMap);
        m_nextId++;
    }

    //
    // Internals
    //

    function calcCreateGasFee(uint128 count) private pure returns (uint128) {
        return CONSTRUCTOR_GAS + count * FEE_CLAIM + FEE_CREATE;
    }

    function buildPoolImage(
        address creator,
        uint256 id
    ) private view returns (TvmCell) {
        TvmBuilder b; b.store(address(this));
        TvmCell code = tvm.setCodeSalt(m_poolCode, b.toCell());
        return tvm.buildStateInit({
            code: code,
            varInit: {id: id, creator: creator},
            contr: VestingPool
        });
    }

    //
    // Getters
    //

    function getPoolCodeHash() external override view returns (uint256 codeHash) {
        TvmBuilder b; b.store(address(this));
        TvmCell code = tvm.setCodeSalt(m_poolCode, b.toCell());
        codeHash = tvm.hash(code);
    }

    function getCreateFee(uint128 claimers) external override pure returns (uint128 fee) {
        fee = calcCreateGasFee(claimers);
    }

    function setPoolImage(TvmCell image) public onlyOwner accept {
        m_poolCode = image.toSlice().loadRef();
    }
    //
    // Upgradable
    // TODO remove before release
    //

    function onCodeUpgrade() internal /*override*/ {
        tvm.resetStorage();
    }
}