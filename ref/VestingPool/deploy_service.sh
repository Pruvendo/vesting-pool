#!/bin/bash
set -e
contract=VestingService

export tos=tonos-cli
export NETWORK=${1:-localhost}

function get_address {
echo $(cat log.log | grep "Raw address:" | cut -d ' ' -f 3)
}

function toscall {
$tos --url $NETWORK call $debot_address $1 $2 --sign $contract.keys.json --abi $contract.abi.json  > /dev/null
}

if [ "${UPDATE:-false}" == "false" ]; then
    echo 1. Generate address
    $tos genaddr $contract.tvc --abi $contract.abi.json --${KEYOPT:-genkey} $contract.keys.json > log.log
    debot_address=$(get_address)

    echo 2. Give initial balance
    bash ../giver.sh $debot_address 1000000000

    echo 3. Deploy and call constructor
    $tos --url $NETWORK deploy $contract.tvc \
        "{\"poolImage\":\"$(base64 -w 0 VestingPool.tvc)\"}" \
        --sign $contract.keys.json \
        --abi $contract.abi.json > /dev/null

    echo 4. Save address to file
    echo -n $debot_address > $contract.addr
    rm log.log
else
    debot_address=$(cat $contract.addr)
    echo 1. Update Vesting Service
    toscall upgrade "{\"state\":\"$(base64 -w 0 $contract.tvc)\"}"
fi

echo $debot_address
echo Completed

