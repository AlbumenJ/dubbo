package org.apache.dubbo.rpc.protocol.tri;

import io.netty.util.AsciiString;

import static io.netty.util.internal.MathUtil.findNextPositivePowerOfTwo;
import static io.netty.util.internal.ObjectUtil.checkNotNull;

public class HttpMethod implements Comparable<HttpMethod> {
    public static final HttpMethod OPTIONS;

    public static final HttpMethod GET;

    public static final HttpMethod HEAD;

    public static final HttpMethod POST;

    public static final HttpMethod PUT;

    public static final HttpMethod PATCH;

    public static final HttpMethod DELETE;

    public static final HttpMethod TRACE;

    public static final HttpMethod CONNECT;

    private static final EnumNameMap<HttpMethod> methodMap;

    static {
        try {
            OPTIONS = new HttpMethod("OPTIONS");
            GET = new HttpMethod("GET");
            HEAD = new HttpMethod("HEAD");
            POST = new HttpMethod("POST");
            PUT = new HttpMethod("PUT");
            PATCH = new HttpMethod("PATCH");
            DELETE = new HttpMethod("DELETE");
            TRACE = new HttpMethod("TRACE");
            CONNECT = new HttpMethod("CONNECT");
            methodMap = new EnumNameMap<HttpMethod>(
                new EnumNameMap.Node<HttpMethod>(OPTIONS.toString(), OPTIONS),
                new EnumNameMap.Node<HttpMethod>(GET.toString(), GET),
                new EnumNameMap.Node<HttpMethod>(HEAD.toString(), HEAD),
                new EnumNameMap.Node<HttpMethod>(POST.toString(), POST),
                new EnumNameMap.Node<HttpMethod>(PUT.toString(), PUT),
                new EnumNameMap.Node<HttpMethod>(PATCH.toString(), PATCH),
                new EnumNameMap.Node<HttpMethod>(DELETE.toString(), DELETE),
                new EnumNameMap.Node<HttpMethod>(TRACE.toString(), TRACE),
                new EnumNameMap.Node<HttpMethod>(CONNECT.toString(), CONNECT));
        } catch (Throwable t) {
            System.out.println("Triple Catch ERROR!!!!" + t.getMessage());
            System.out.println("Triple Catch ERROR!!!!" + t.toString());
            t.printStackTrace();
            throw t;
        }
    }

    /**
     * Returns the {@link HttpMethod} represented by the specified name.
     * If the specified name is a standard HTTP method name, a cached instance
     * will be returned.  Otherwise, a new instance will be returned.
     */
    public static HttpMethod valueOf(String name) {
        HttpMethod result = methodMap.get(name);
        return result != null ? result : new HttpMethod(name);
    }

    private final AsciiString name;

    /**
     * Creates a new HTTP method with the specified name.  You will not need to
     * create a new method unless you are implementing a protocol derived from
     * HTTP, such as
     * <a href="https://en.wikipedia.org/wiki/Real_Time_Streaming_Protocol">RTSP</a> and
     * <a href="https://en.wikipedia.org/wiki/Internet_Content_Adaptation_Protocol">ICAP</a>
     */
    public HttpMethod(String name) {
        name = checkNotNull(name, "name").trim();
        if (name.isEmpty()) {
            throw new IllegalArgumentException("empty name");
        }

        for (int i = 0; i < name.length(); i++) {
            char c = name.charAt(i);
            if (Character.isISOControl(c) || Character.isWhitespace(c)) {
                throw new IllegalArgumentException("invalid character in name");
            }
        }

        this.name = AsciiString.cached(name);
    }

    /**
     * Returns the name of this method.
     */
    public String name() {
        return name.toString();
    }

    /**
     * Returns the name of this method.
     */
    public AsciiString asciiName() {
        return name;
    }

    @Override
    public int hashCode() {
        return name().hashCode();
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (!(o instanceof HttpMethod)) {
            return false;
        }

        HttpMethod that = (HttpMethod) o;
        return name().equals(that.name());
    }

    @Override
    public String toString() {
        return name.toString();
    }

    @Override
    public int compareTo(HttpMethod o) {
        if (o == this) {
            return 0;
        }
        return name().compareTo(o.name());
    }

    private static final class EnumNameMap<T> {
        private final EnumNameMap.Node<T>[] values;
        private final int valuesMask;

        EnumNameMap(EnumNameMap.Node<T>... nodes) {
            values = (EnumNameMap.Node<T>[]) new EnumNameMap.Node[findNextPositivePowerOfTwo(nodes.length)];
            valuesMask = values.length - 1;
            for (EnumNameMap.Node<T> node : nodes) {
                int i = hashCode(node.key) & valuesMask;
                if (values[i] != null) {
                    throw new IllegalArgumentException("index " + i + " collision between values: [" +
                        values[i].key + ", " + node.key + ']');
                }
                values[i] = node;
            }
        }

        T get(String name) {
            EnumNameMap.Node<T> node = values[hashCode(name) & valuesMask];
            return node == null || !node.key.equals(name) ? null : node.value;
        }

        private static int hashCode(String name) {
            // This hash code needs to produce a unique index in the "values" array for each HttpMethod. If new
            // HttpMethods are added this algorithm will need to be adjusted. The constructor will "fail fast" if there
            // are duplicates detected.
            // For example with the current set of HttpMethods it just so happens that the String hash code value
            // shifted right by 6 bits modulo 16 is unique relative to all other HttpMethod values.
            return name.hashCode() >>> 6;
        }

        private static final class Node<T> {
            final String key;
            final T value;

            Node(String key, T value) {
                this.key = key;
                this.value = value;
            }
        }
    }
}
