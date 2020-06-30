// RUN: true

#include <iostream>
#include <CL/sycl.hpp>

#include "../utilities/device_selectors.hpp"

using namespace cl::sycl;

class event_wait;

int main() {
  selector_defines::CompiledForDeviceSelector selector;
  queue q{selector, property::queue::enable_profiling()};

  auto e = q.submit([&](handler &cgh) {
      int w = 512;
      cgh.single_task<class event_wait>([=]() mutable {
        for (int i = 0; i < 512000; ++i)
          ++w;
      });
      printf("%d \n", w);
  });

  auto nsTimeEnd =
      e.get_profiling_info<info::event_profiling::command_end>();
  auto nsTimeStart =
      e.get_profiling_info<info::event_profiling::command_start>();
  auto duration = nsTimeEnd - nsTimeStart;
  std::cout << "Kernel Duration: " << duration << " ns \n";

  return 0;
}
