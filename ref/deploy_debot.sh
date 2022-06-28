#!/bin/bash
set -e

function get_address {
echo $(cat log.log | grep "Raw address:" | cut -d ' ' -f 3)
}

if [ -z $tos ]; then
    tos=tonos-cli
fi

echo GENADDR $1 ----------------------------------------------
$tos genaddr $1.tvc --abi $1.abi.json --${KEYOPT:-genkey} $1.keys.json > log.log
DEBOT_ADDRESS=$(get_address)
echo GIVER $1 ------------------------------------------------
bash ${0%/*}/giver.sh $DEBOT_ADDRESS 2000000000
echo DEPLOY $1 -----------------------------------------------
$tos --url $NETWORK deploy $1.tvc "{}" --sign $1.keys.json --abi $1.abi.json
DEBOT_ABI=$(cat $1.abi.json | xxd -ps -c 20000)
$tos --url $NETWORK call $DEBOT_ADDRESS setABI "{\"dabi\":\"$DEBOT_ABI\"}" --sign $1.keys.json --abi $1.abi.json
echo -n $DEBOT_ADDRESS > $1.addr
