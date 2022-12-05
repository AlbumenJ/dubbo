package org.apache.dubbo.rpc.protocol.rest.netty4;

import org.apache.dubbo.rpc.Invoker;
import org.apache.dubbo.rpc.PathResolver;

import java.util.concurrent.ConcurrentHashMap;

public class RestPathResolver implements PathResolver {

    private final ConcurrentHashMap<String, Invoker<?>> path2Invoker = new ConcurrentHashMap<>();

    @Override
    public void add(String path, Invoker<?> invoker) {
        path2Invoker.put(path, invoker);
    }

    @Override
    public Invoker<?> resolve(String path) {
        return path2Invoker.get(path);
    }

    public Invoker<?> resolve(String path, String method, String group, String version) {
        return path2Invoker.get(path);
    }

    @Override
    public boolean hasNativeStub(String path) {
        throw new UnsupportedOperationException();
    }

    @Override
    public void addNativeStub(String path) {
        throw new UnsupportedOperationException();
    }

    @Override
    public void remove(String path) {
        path2Invoker.remove(path);
    }

    @Override
    public void destroy() {
        path2Invoker.clear();
    }
}
