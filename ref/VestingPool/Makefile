tvcs = VestingService.tvc VestingPool.tvc VestingAPI.tvc
all: $(tvcs)

$(tvcs): %.tvc: %.sol
	everdev sol compile $^

clean:
	rm -f *.tvc *.abi.json
	rm -rf .solc_imports

rebuild: clean all

deployalldev:
	bash deploy_service.sh net.ton.dev
	bash deploy_helper.sh net.ton.dev

updservice: all
	UPDATE=true ./deploy_service.sh net.ton.dev

updapi: all
	UPDATE=true ./deploy_helper.sh net.ton.dev

allpools:
	tonos-cli debot start `cat VestingAPI.addr` --pipechain ./manifests/get-pools.json

onepool:
	tonos-cli debot start `cat VestingAPI.addr` --pipechain ./manifests/pool-info.json

createpool:
	tonos-cli debot start `cat VestingAPI.addr` --pipechain ./manifests/create-pool.json

claim:
	tonos-cli debot start `cat VestingAPI.addr` --pipechain ./manifests/claim.json

unlock:
	tonos-cli debot start `cat VestingAPI.addr` --pipechain ./manifests/unlock.json