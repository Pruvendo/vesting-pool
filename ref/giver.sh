#!/bin/bash
set -e

if [ -z $tos ]; then
    tos=tonos-cli
fi

if [ -z $NETWORK ]; then
    NETWORK=http://127.0.0.1
fi

if [ -z $giver ]; then
    if [ "$NETWORK" == "net.ton.dev" ]; then
        giver=0:2bb4a0e8391e7ea8877f4825064924bd41ce110fce97e939d3323999e1efbb13
    else 
        if [ "$NETWORK" == "main.ton.dev" ]; then
            giver=0:4e61670f7f1fa12dbdcc17b256eea19da937a993a05ff11e0b72f92108608e73
        else 
            giver=0:841288ed3b55d9cdafa806807f02a0ae0c169aa5edfe88a789a6482429756a94
        fi
    fi
fi

if [ "$NETWORK" == "net.ton.dev" ]; then
    $tos --url $NETWORK call --abi ~/giverv2.abi.json --sign ~/giver.keys.json $giver sendTransaction "{\"dest\":\"$1\",\"value\":$2,\"bounce\":false}" > /dev/null
else
    if [ "$NETWORK" == "main.ton.dev" ]; then
        $tos --url $NETWORK call --abi ${0%/*}/SafeMultisigWallet.abi.json $giver sendTransaction "{\"dest\":\"$1\",\"value\":$2,\"bounce\":false,\"flags\":3,\"payload\":\"\"}" --sign ~/maingiver.keys.json > /dev/null
    else 
        $tos --url $NETWORK call --abi ~/local_giver.abi.json $giver sendGrams "{\"dest\":\"$1\",\"amount\":$2}" > /dev/null
    fi
fi
