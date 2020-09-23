/* Taken from:
 * Herb Sutter, Exception-Safe Generic Containers
 * C++ Report, 9(8), September 1997.
 * http://ptgmedia.pearsoncmg.com/imprint_downloads/informit/aw/meyerscddemo/DEMO/MAGAZINE/SU_FRAME.HTM
 */

template <class T> class Stack {
public:
  Stack()
    : v_(new T[10]),
      vsize_(10),
      vused_(0)
  { }

  ~Stack() {
    delete[] v_;
  }

  Stack( const Stack<T>& other )
    : v_(NewCopy( other.v_,
                  other.vsize_,
                  other.vsize_ )),
      vsize_(other.vsize_),
      vused_(other.vused_)
  { }

  Stack<T>&
  operator=( const Stack<T>& other ) {
    if( this != &other ) {
      T* v_new = NewCopy( other.v_,
                          other.vsize_,
                          other.vsize_ );
      delete[] v_;
      v_ = v_new;
      vsize_ = other.vsize_;
      vused_ = other.vused_;
    }
    return *this;
  }

  size_t Size() const {
    return vused_;
  }

  void Push(const T&) {
    if( vused_ == vsize_ ) {
      size_t vsize_new = vsize_*2+1;
      T* v_new = NewCopy( v_, vsize_, vsize_new );
      delete[] v_;
      v_ = v_new;
      vsize_ = vsize_new;
    }
    v_[vused_] = t;
    ++vused_;
  }

  T Pop() {
    if( vused_ == 0 ) {
      throw "pop from empty stack";
    } else {
      T result = v_[vused_-1];
      --vused_;
      return result;
    }
  }

private:
  T*     v_;
  size_t vsize_;
  size_t vused_;

  T* NewCopy( const T* src,
              size_t   srcsize,
              size_t   destsize ) {
    assert( destsize >= srcsize );
    T* dest = new T[destsize];
    try {
      copy( src, src+srcsize, dest );
    } catch(...) {
      delete[] dest;
      throw;
    }
    return dest;
  }
};


// Exception safe version:

template <class T> class StackImpl {
protected:
  StackImpl(size_t size=0)
    : v_( static_cast<T*>
          ( size == 0
            ? 0
            : ::operator new(sizeof(T)*size) ) ),
      vsize_(size),
      vused_(0)
  { }

  ~StackImpl() {
    destroy( v_, v_+vused_ );
    ::operator delete( v_ );
  }

  void Swap(StackImpl& other) throw() {
    swap(v_, other.v_);
    swap(vsize_, other.vsize_);
    swap(vused_, other.vused_);
  }

  T*     v_;
  size_t vsize_;
  size_t vused_;
};

template <class T>
class Stack : private StackImpl<T> {
public:
  Stack(size_t size=0) : StackImpl<T>(size) { }

  Stack(const Stack& other)
    : StackImpl<T>(other.vused_)
  {
    while( vused_ < other.vused_ ) {
      construct( v_+vused_,
                 other.v_[vused_] );
      ++vused_;
    }
  }

  Stack& operator=(const Stack& other) {
    Stack temp(other);
    Swap( temp );
    return *this;
  }

  size_t Size() const {
    return vused_;
  }

  void Push( const T& t ) {
    if( vused_ == vsize_ ) {
      Stack temp( vsize_*2+1 );
      while( temp.Count() < vused_ ) {
        temp.Push( v_[temp.Count()] );
      }
      temp.Push( t );
      Swap( temp );
    } else {
      construct( v_+vused_, t );
      ++vused_;
    }
  }

  T& Top() {
    if( vused_ == 0) {
      throw "empty stack";
    }
    return v_[vused_-1];
  }

  void Pop() {
    if( vused_ == 0) {
      throw "pop from empty stack";
    } else {
      --vused_;
      destroy( v_+vused_ );
    }
  }
};

class T {
public:
  T() {
    if (*)
      throw;
  }

  T(const &T) {
    if (*)
      throw;
  }

  T& operator=(const T&) {
    if (*)
      throw;
  }
};

int main() {
  Stack<T> S;
  S.push(T());
  S.push(T());
  size_t s = S.size();
  T t = S.pop();

  return 0;
}
