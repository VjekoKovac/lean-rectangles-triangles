The recorded run took place on a Linux host with no /root directory and a
restriction on configuring a new loopback interface. run.sh supplies an outer
filesystem layout with /root. offline-bwrap supplies an outer empty network
namespace to the nested build sandbox. Lake's sandbox remains enabled. The
first direct attempt is recorded in host-initial-attempt.txt. On an ordinary
compatible Linux host use bash scripts/compare.sh directly.
