//==---------------- managed_global.hpp -------------------------*- C++-*---==//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#pragma once

#include <sycl/detail/defines.hpp>

#include <atomic>
#include <cassert>
#include <mutex>
#include <shared_mutex>
#include <utility>

namespace sycl {
__SYCL_INLINE_VER_NAMESPACE(_V1) {
namespace detail {

/// Stores an object of Type T, but let the user manually call the constructor
/// and destructor.
/// If build in debug mode whether the object is constructed or not is going to
/// be tracked and asserted for.
template <typename T> class ManagedObj {
#ifndef NDEBUG
  bool is_constructed = false;
#endif
  std::aligned_storage_t<sizeof(T), alignof(T)> data;
  T &get_internal() { return *(T *)&data; }

public:
  ManagedObj() = default;
  ManagedObj(const T &) = delete;
  ManagedObj &operator=(const T &) = delete;

  template <typename... Ts> void construct(Ts &&...ts) {
    assert(!is_constructed && (is_constructed = true));
    new (&data) T(std::forward<Ts>(ts)...);
  }
  void destruct() {
    assert(is_constructed && !(is_constructed = false));
    get_internal().~T();
  }
  T &get() {
    assert(is_constructed);
    return get_internal();
  }
  const T &get() const { return const_cast<ManagedObj *>(this)->get(); }
#ifndef NDEBUG
  ~ManagedObj() { assert(!is_constructed); }
#endif
};

/// Stores an object of of type T. with manged lifetime.
/// The lifetime starts when the object is not constructed and a GlobalRefCount
/// is created The lifetime ens when the last GlobalRefCount is destructed. It
/// is safe to concurrently execute multiple init_or_inc_ref_count and
/// dec_ref_count. The user should always access the global variable stored
/// inside the ManagedGlobal via a GlobalRefCount
template <typename T> class ManagedGlobal {
  ManagedObj<T> data;

  std::atomic<uint32_t> ref_count = 0;
  std::shared_mutex mtx;

  template <auto> friend class GlobalRefCount;
  using value_type = T;

  void init_or_inc_ref_count() {
    {
      std::shared_lock<std::shared_mutex> reader(mtx);
      uint32_t count = ref_count;
      if (count > 0 && ref_count.compare_exchange_strong(count, count + 1))
        return;
    }
    std::lock_guard<std::shared_mutex> g(mtx);
    if (ref_count > 0) {
      ref_count++;
      return;
    }
    data.construct();
    ref_count++;
  }

  void dec_ref_count_and_maybe_destroy() {
    assert(ref_count > 0);
    {
      std::shared_lock<std::shared_mutex> reader(mtx);
      uint32_t count = ref_count;
      if (count > 1 && ref_count.compare_exchange_strong(count, count - 1))
        return;
    }
    std::lock_guard<std::shared_mutex> g(mtx);
    if (ref_count > 1) {
      ref_count--;
      return;
    }
    data.destruct();
    ref_count--;
  }

public:
  T &get() { return data.get(); }
  const T &get() const { return data.get(); }
};

/// Keep a global variable a live during its lifetime.
/// This allows to have a global state that isn't destroyed as part of global
/// destructors. but when ever its last use runs out avoiding the global
/// destructor ordering issue. This class is empty so it should be inherited by
/// object that need access to the global.
/// It is safe to concurrently execute create and destroy GlobalRefCount objects.
template <auto Global> class GlobalRefCount {
  using T = typename std::remove_pointer_t<decltype(Global)>::value_type;

public:
  T &get() { return Global->get(); }
  const T &get() const { return Global->get(); }
  GlobalRefCount() { Global->init_or_inc_ref_count(); }
  ~GlobalRefCount() { Global->dec_ref_count_and_maybe_destroy(); }
};

}  // namespace detail
}  // namespace sycl
}
