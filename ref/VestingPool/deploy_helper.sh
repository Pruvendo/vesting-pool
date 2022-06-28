#!/bin/bash
set -e
filename=VestingAPI
filenamesol=$filename.sol
filenameabi=$filename.abi.json
filenametvc=$filename.tvc
filenamekeys=$filename.keys.json

export tos=tonos-cli
export NETWORK=${1:-localhost}

function toscall {
$tos --url $NETWORK call $debot_address $1 $2 --sign $filenamekeys --abi $filenameabi > /dev/null
}

if [ "${UPDATE:-false}" == "false" ]; then
    echo 1. Deploy DeBot and set ABI
    bash ../deploy_debot.sh $filename > /dev/null
    debot_address=$(cat $filename.addr)
else
    debot_address=$(cat $filename.addr)
    echo 1. Update DeBot
    toscall upgrade "{\"state\":\"$(base64 -w 0 $filename.tvc)\"}"
    echo 2. Set ABI
    dabi=$(cat $filename.abi.json | jq 'del(.fields)' | tr -d '[:space:]' | xxd -ps -c 30000 )
    toscall setABI "{\"dabi\":\"$dabi\"}"
fi

echo 3. Set Service 
toscall setService "{\"addr\":\"$(cat VestingService.addr)\"}"
echo DONE
if [ "${UPDATE:-false}" == "false" ]; then
    echo -n $debot_address > $filename.addr
fi

