#!/usr/bin/env bash
# Trusted bootstrap in the fresh Ubuntu 26.04 guest, before any proof is compiled.
set -euo pipefail
cd /srv/ots-benchmark
systemctl --version
cat /sys/kernel/security/lsm
test "$(systemctl --version | head -1 | awk '{print $2}')" -ge 257
grep -qw landlock /sys/kernel/security/lsm
# ProtectSystem=strict excludes /home; keep the judge home under /srv, as upstream does.
useradd --create-home --home-dir /srv/ots --shell /bin/bash ots
chown -R ots:ots /srv/ots-benchmark
mkdir /var/lib/ots-work
mkfs.ext4 -q -F -m 0 -E nodiscard,lazy_itable_init=0,lazy_journal_init=0 /dev/vdb
mount -o nosuid,nodev /dev/vdb /var/lib/ots-work
chown ots:ots /var/lib/ots-work
loginctl enable-linger ots
systemctl start "user@$(id -u ots).service"
cat > /etc/apparmor.d/ots-systemd-executor <<'APPARMOR'
abi <abi/4.0>,
include <tunables/global>
profile ots-systemd-executor /usr/lib/systemd/systemd-executor flags=(unconfined) {
  userns,
  include if exists <local/ots-systemd-executor>
}
APPARMOR
apparmor_parser -r /etc/apparmor.d/ots-systemd-executor
sudo -u ots -H bash -euo pipefail <<'SETUP'
curl --fail --location --retry 3 https://raw.githubusercontent.com/leanprover/elan/v4.2.4/elan-init.sh \
  -o /srv/ots/elan-init.sh
sh /srv/ots/elan-init.sh -y --default-toolchain none
bash .yukon/setup.sh
export OTS_WORK_DIR=/var/lib/ots-work TMPDIR=/var/lib/ots-work
python3 .contract/verifier/check_linux_sandbox.py
SETUP
