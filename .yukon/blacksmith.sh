#!/usr/bin/env bash
# The Blacksmith host lacks Landlock. Boot the verifier's supported OS with KVM.
set -euo pipefail
cd "$(dirname "$0")/.."
vm="${RUNNER_TEMP:?This entry point runs in GitHub Actions}/ots-verifier-vm"
ssh_args=(-i "${vm}/key" -p 2222 -o BatchMode=yes -o ConnectTimeout=5
  -o ServerAliveInterval=15 -o ServerAliveCountMax=4
  -o StrictHostKeyChecking=accept-new -o UserKnownHostsFile="${vm}/known_hosts")
# Callers supply fixed commands; the only variable command argument is allowlisted below.
# shellcheck disable=SC2029
guest() { ssh "${ssh_args[@]}" ubuntu@127.0.0.1 "$@"; }

case "${1:-}" in
  setup)
    test -c /dev/kvm || { echo 'Blacksmith x64 nested KVM is required' >&2; exit 1; }
    sudo apt-get update -qq
    sudo apt-get install -y --no-install-recommends qemu-system-x86 qemu-utils cloud-image-utils
    mkdir -m 700 "${vm}"
    curl --fail --location --retry 3 \
      https://cloud-images.ubuntu.com/releases/resolute/release-20260918/ubuntu-26.04-server-cloudimg-amd64.img \
      -o "${vm}/ubuntu.img"
    echo "4908fb59ccd4e87ae4e8e973b7ef56f535448eacb24a87fd787270c0048987bc  ${vm}/ubuntu.img" | sha256sum --check
    qemu-img create -f qcow2 -F qcow2 -b "${vm}/ubuntu.img" "${vm}/root.qcow2" 100G
    # Allocate all backing storage before exposing the separate disk to the judge.
    fallocate -l 48G "${vm}/work.raw"
    ssh-keygen -q -t ed25519 -N '' -f "${vm}/key"
    cat > "${vm}/user-data" <<CLOUD
#cloud-config
ssh_authorized_keys:
  - $(cat "${vm}/key.pub")
package_update: true
packages:
  - git
  - curl
  - build-essential
  - python3
  - golang-go
  - dbus-user-session
  - apparmor
  - zstd
CLOUD
    printf 'instance-id: ots-verifier\nlocal-hostname: ots-verifier\n' > "${vm}/meta-data"
    cloud-localds "${vm}/seed.img" "${vm}/user-data" "${vm}/meta-data"
    sudo qemu-system-x86_64 -accel kvm -cpu host -smp 28 -m 80G \
      -drive "file=${vm}/root.qcow2,if=virtio,format=qcow2" \
      -drive "file=${vm}/work.raw,if=virtio,format=raw,cache=none" \
      -drive "file=${vm}/seed.img,if=virtio,format=raw,readonly=on" \
      -netdev user,id=net0,hostfwd=tcp:127.0.0.1:2222-:22 -device virtio-net-pci,netdev=net0 \
      -display none -serial "file:${vm}/console.log" -monitor none \
      -daemonize -pidfile "${vm}/qemu.pid"
    ready=0
    for ((attempt=0; attempt<120; attempt++)); do
      if guest true 2>/dev/null; then ready=1; break; fi
      sleep 2
    done
    if [[ "${ready}" != 1 ]]; then sudo cat "${vm}/console.log"; exit 1; fi
    guest 'sudo cloud-init status --wait'
    # Credentials were removed by checkout; only the checkout enters the VM.
    tar --exclude='./benchmark-results' -cf - . | \
      guest 'sudo mkdir -p /srv/ots-benchmark && sudo tar -xf - -C /srv/ots-benchmark'
    guest 'sudo bash /srv/ots-benchmark/.yukon/vm-setup.sh'
    ;;
  run)
    track="${2:?track required}"
    # Only manifest track names can enter the remote shell command.
    case "${track}" in
      lower-generality-1|lower-generality-2|lower-generality-3|upper-compressions|upper-riscv) ;;
      *) echo "Unknown track: ${track}" >&2; exit 1 ;;
    esac
    guest "cd /srv/ots-benchmark && sudo -u ots -H env OTS_WORK_DIR=/var/lib/ots-work TMPDIR=/var/lib/ots-work python3 .yukon/run.py ${track}"
    ;;
  collect)
    mkdir -p benchmark-results
    if [[ -f "${vm}/qemu.pid" ]]; then
      guest 'sudo mkdir -p /srv/ots-benchmark/benchmark-results && sudo tar -C /srv/ots-benchmark/benchmark-results -cf - .' | tar -xf - -C benchmark-results
    fi
    ;;
  stop)
    if [[ -f "${vm}/qemu.pid" ]]; then sudo kill "$(sudo cat "${vm}/qemu.pid")"; fi
    ;;
  *) echo 'Usage: blacksmith.sh setup | run TRACK | collect | stop' >&2; exit 2 ;;
esac
