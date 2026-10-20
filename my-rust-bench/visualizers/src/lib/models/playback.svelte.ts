export function createPlayback(getStepsCount: () => number, initialSpeed = 1500) {
  let stepIdx = $state(0);
  let isPlaying = $state(false);
  let speed = $state(initialSpeed);

  $effect(() => {
    if (!isPlaying) return;
    const timer = setTimeout(() => {
      if (stepIdx < getStepsCount() - 1) {
        stepIdx += 1;
      } else {
        isPlaying = false;
      }
    }, speed);
    return () => clearTimeout(timer);
  });

  return {
    get stepIdx() {
      return stepIdx;
    },
    set stepIdx(v: number) {
      stepIdx = v;
    },
    get isPlaying() {
      return isPlaying;
    },
    set isPlaying(v: boolean) {
      isPlaying = v;
    },
    get speed() {
      return speed;
    },
    set speed(v: number) {
      speed = v;
    },
    reset() {
      stepIdx = 0;
      isPlaying = false;
    }
  };
}
